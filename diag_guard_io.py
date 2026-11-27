from __future__ import annotations

import ast as _ast
import contextlib as _contextlib
import contextvars as _contextvars
import difflib
import errno
import hashlib
import io
import logging
import os
import re
import shutil as _shutil
import tempfile as _tempfile
import threading
import time as _time
import tokenize
from collections.abc import Callable, Sequence
from pathlib import Path as _Path
from typing import Any, NamedTuple

from jwsgj.diag_shared_ast_views import (
    LexicalScopeTable,
    call_head_is_shadowed,
    call_scope_map,
    collect_lexical_scope_table,
    scope_import_tables,
)
from jwsgj.diag_shared_source_core import (
    read_source_with_fingerprint,
)
from jwsgj.diag_shared_source_scan import (
    check_s02_portal_file,
    ensure_os_import,
)
from jwsgj.diag_types_defs import ContractViolationError
from jwsgj.diag_types_vocab import (
    MSG_EXCEPTION_BROAD_HANDLER,
    MSG_OSERROR_SUPPRESSED,
    PARSE_DEGRADE_EXC,
    PROJECT_ROOT_MARKERS,
)
from jwsgj.log_config import locked_artifact, log_swallowed, safe_write_audit
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_backup_base
from jwsgj.runtime_scope import canonical_path

_log = logging.getLogger(__name__)
JSON_READ_DEGRADE_EXC = (OSError, ValueError, RecursionError, MemoryError)
__all__ = [
    'JSON_READ_DEGRADE_EXC',
    'SHFILEOP_TIMEOUT_S',
    'SKILL_DOC_FILENAME',
    'SourceReadError',
    '_within_any_root',
    'archive_backup',
    'atomic_replace_bytes',
    'atomic_write_text',
    'backup_file_name',
    'backup_path_for',
    'bytes_fingerprint',
    'check_path_traversal',
    'cleanup_backup_dir',
    'coerce_target_file',
    'compile_error',
    'content_fingerprint',
    'decode_source_strict',
    'detect_newline',
    'detect_source_encoding',
    'diagnosis_readonly_scope',
    'discard_tmp_file',
    'format_diff_preview',
    'fs_path_text',
    'get_diag_readonly_violations',
    'guarded_open',
    'guarded_write',
    'materialize_backup',
    'move_to_recycle_bin',
    'normalize_fs_key',
    'normalize_out_path',
    'normalize_path_arg',
    'path_identity',
    'read_source_text_strict',
    'read_text_bom',
    'register_l2l3_write_verifier',
    'replace_with_retry',
    'resolve_skill_dir',
    'resolve_within_root',
    'run_verify_guarded',
    'safe_delete',
    'safe_write_text',
    'sandbox_path',
    'sequenced_backup_path',
    'split_tokenizer_lines',
    'two_level_rmtree',
    'two_level_unlink',
    'validate_skill_boundary',
    'verify_syntax',
    'verify_write_degradation',
    'write_backup_bytes',
    'write_text_atomic',
]
_DEFAULT_TEXT_ENCODING = "utf-8"
_DEFAULT_GUARDED_WRITE_STRICT = True
_FINGERPRINT_ENCODING = "utf-8"
_UTF8_SIG_ENCODING = "utf-8-sig"
_UTF8_BOM_BYTES = b"\xef\xbb\xbf"
_DEFAULT_FILE_MODE = 0o644
_BAK_KEEP = 3
_SKIP_BACKUP_SUFFIXES = frozenset({
    ".json", ".jsonl", ".pkl", ".db", ".sqlite", ".csv", ".tsv", ".lock",
})
_BAK_TAIL_RE = re.compile(r"^\d{8}_\d{6}(?:_\d{9})?$")
def _locate_project_root(fp: _Path) -> _Path | None:
    current = fp.parent
    while True:
        if any((current / marker).exists()
               for marker in PROJECT_ROOT_MARKERS):
            return current
        parent = current.parent
        if parent == current:
            return None
        current = parent
def _rotate_stale_backups(temp_dir: _Path, prefix: str) -> None:
    try:
        _cands = _collect_backup_candidates(temp_dir, prefix)
        _prune_backup_candidates(_cands)
    except OSError as _bak_err:
        _log.debug("[guarded_write] 备份轮转清理失败(忽略): %s", _bak_err)
def _collect_backup_candidates(temp_dir: _Path, prefix: str) -> list[tuple[float, _Path]]:
    cands: list[tuple[float, _Path]] = []
    for _p in temp_dir.iterdir():
        try:
            if not _p.is_file():
                continue
            if not (_p.name.startswith(prefix)
                    and _BAK_TAIL_RE.match(_p.name[len(prefix):]) is not None):
                continue
            cands.append((_p.stat().st_mtime, _p))
        except OSError:
            _log.debug("[guarded_write] 轮转候选收集失败(跳过): %s", _p)
    return cands
def _prune_backup_candidates(cands: list[tuple[float, _Path]]) -> None:
    for _, _old in sorted(cands, key=lambda t: t[0])[:-_BAK_KEEP]:
        try:
            if not safe_delete(str(_old)):
                _log.debug(
                    "[guarded_write] 旧备份回收站清理失败(跳过继续): %s",
                    _old)
        except OSError as _one_err:
            _log.debug("[guarded_write] 旧备份删除失败(跳过继续): %s: %s",
                       _old, _one_err)
def _should_skip_backup(fp: _Path) -> bool:
    return fp.suffix.lower() in _SKIP_BACKUP_SUFFIXES or not fp.exists()
def _backup_before_write(filepath: str) -> str | None:
    fp = _Path(filepath)
    if _should_skip_backup(fp):
        return None
    project_root = _locate_project_root(fp)
    if project_root is None:
        _log.warning(
            "[guarded_write] 未找到项目根目录标记，跳过备份: %s", filepath
        )
        return None
    temp_dir = _Path(get_backup_base(str(project_root)))
    try:
        temp_dir.mkdir(parents=True, exist_ok=True)
    except OSError as e:
        _log.error("[guarded_write] 备份目录创建失败 %s: %s", temp_dir, e)
        safe_write_audit("guard_backup_failed", path=filepath,
                         stage="mkdir", error=str(e))
        raise ValueError(
            f"备份失败（目录创建失败），已阻断写入: {filepath}: {e}") from e
    timestamp = _time.strftime("%Y%m%d_%H%M%S")
    backup_name = f"{fp.name}.bak.{timestamp}"
    try:
        backup_path = _unique_backup_path(temp_dir, backup_name)
    except OSError as e:
        _log.error("[guarded_write] 备份路径预留失败 %s: %s", filepath, e)
        safe_write_audit("guard_backup_failed", path=filepath,
                         stage="reserve", error=str(e))
        raise ValueError(f"备份失败（路径预留），已阻断写入: {filepath}: {e}") from e
    return _copy_to_backup(fp, backup_path, temp_dir, filepath)
def _copy_to_backup(fp: _Path, backup_path: _Path, temp_dir: _Path,
                    filepath: str) -> str:
    try:
        _shutil.copy2(str(fp), str(backup_path))
        _log.info("[guarded_write] 已备份 %s -> %s", fp.name, backup_path)
        try:
            os.utime(str(backup_path), None)
        except OSError:
            _log.debug("[guarded_write] 备份产物 mtime touch 失败(保留源 mtime): %s",
                       backup_path)
        _rotate_stale_backups(temp_dir, f"{fp.name}.bak.")
        return str(backup_path)
    except OSError as e:
        _log.error("[guarded_write] 备份失败 %s: %s", filepath, e)
        safe_write_audit("guard_backup_failed", path=filepath,
                         stage="copy", error=str(e))
        _cleanup_tmp_artifact(
            str(backup_path), "[guarded_write] 失败备份", warn=True)
        raise ValueError(f"备份失败，已阻断写入: {filepath}: {e}") from e
def _unique_backup_path(temp_dir: _Path, backup_name: str) -> _Path:
    backup_path = temp_dir / backup_name
    _ns = _time.time_ns() % 1_000_000_000
    while True:
        try:
            fd = os.open(str(backup_path),
                         os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o666)
        except FileExistsError:
            _ns = (_ns + 1) % 1_000_000_000
            backup_path = temp_dir / f"{backup_name}_{_ns:09d}"
            continue
        os.close(fd)
        return backup_path
def _strip_tmp_suffix(fp: str) -> str:
    parts = fp.split(".")
    if len(parts) >= 2 and parts[-1].lower() == "tmp":
        parts.pop()
        while parts and parts[-1].isdigit():
            parts.pop()
    return ".".join(parts)
def _read_existing_text(filepath: str, encoding: str, *,
                       strict: bool) -> str | None:
    if not os.path.isfile(filepath):
        return None
    try:
        with open(filepath, encoding=encoding, newline="") as _f:
            return _f.read()
    except (OSError, UnicodeDecodeError) as e:
        if not strict:
            _log.warning(
                "[guard_io] guarded_write: 已有文件读取失败"
                "(危险检查按无旧内容口径执行, 幂等不跳过): %s", e)
            return None
        _log.error("[guard_io] 追加模式读取已有文件失败,已阻断写入"
                   "(原文件保持原状): %s: %s", filepath, e)
        safe_write_audit("guarded_append_read_failed", path=filepath,
                         error=str(e))
        raise OSError(
            f"追加模式读取已有文件失败，已阻断写入以保护原内容: {filepath}: {e}") from e
def _danger_line_at(content: str, position: int) -> str:
    line_start = content.rfind("\n", 0, position) + 1
    line_end = content.find("\n", position)
    return content[line_start:line_end if line_end >= 0 else len(content)].strip()
def _danger_spans(content: str | None) -> list[tuple[int, int]] | None:
    if not content:
        return []
    return _literal_token_spans(content)
def _danger_line_hits(pattern: re.Pattern[str], content: str | None,
                      spans: list[tuple[int, int]] | None = None
                      ) -> dict[str, int]:
    hits: dict[str, int] = {}
    text = content or ""
    for match in pattern.finditer(text):
        if spans is not None and _inside_any_span(match.start(), spans):
            continue
        key = _danger_line_at(text, match.start())
        hits[key] = hits.get(key, 0) + 1
    return hits
def _static_literal_truth(node: _ast.expr) -> bool | None:
    if isinstance(node, _ast.Constant):
        return bool(node.value)
    if isinstance(node, _ast.UnaryOp):
        if isinstance(node.op, _ast.Not):
            operand_truth = _static_literal_truth(node.operand)
            return None if operand_truth is None else not operand_truth
        if (isinstance(node.op, (_ast.UAdd, _ast.USub))
                and isinstance(node.operand, _ast.Constant)
                and isinstance(node.operand.value, (int, float, complex))):
            return bool(node.operand.value)
        if (isinstance(node.op, _ast.Invert)
                and isinstance(node.operand, _ast.Constant)
                and isinstance(node.operand.value, int)):
            return bool(~node.operand.value)
    if isinstance(node, (_ast.List, _ast.Tuple, _ast.Set)):
        if any(not isinstance(item, _ast.Starred) for item in node.elts):
            return True
        if not node.elts:
            return False
        values = [_static_iterable_truth(item.value) for item in node.elts]
        if any(value is True for value in values):
            return True
        return False if all(value is False for value in values) else None
    if isinstance(node, _ast.Dict):
        if any(key is not None for key in node.keys):
            return True
        if not node.keys:
            return False
        values = [_static_literal_truth(value) for value in node.values]
        if any(value is True for value in values):
            return True
        return False if all(value is False for value in values) else None
    return None
def _static_iterable_truth(node: _ast.expr) -> bool | None:
    if (isinstance(node, (_ast.List, _ast.Tuple, _ast.Set, _ast.Dict))
            or (isinstance(node, _ast.Constant)
                and isinstance(node.value, (str, bytes)))):
        return _static_literal_truth(node)
    return None
_LITERAL_SHELL_MISSING = object()
def _literal_dict_shell_truth(node: _ast.expr) -> Any:
    if not isinstance(node, _ast.Dict):
        return None
    result: Any = _LITERAL_SHELL_MISSING
    for key, value in zip(node.keys, node.values):
        if key is None:
            if isinstance(value, _ast.Dict) and not value.keys:
                continue
            result = None
        elif isinstance(key, _ast.Constant) and key.value == "shell":
            result = _static_literal_truth(value)
    return result
def _subprocess_shell_truth(node: _ast.Call) -> Any:
    result: Any = _LITERAL_SHELL_MISSING
    for keyword in node.keywords:
        if keyword.arg == "shell":
            result = _static_literal_truth(keyword.value)
        elif keyword.arg is None:
            unpacked = _literal_dict_shell_truth(keyword.value)
            if unpacked is not _LITERAL_SHELL_MISSING:
                result = unpacked
    return result
def _describe_dangerous_call(node: _ast.Call) -> str | None:
    func = node.func
    if isinstance(func, _ast.Name):
        return _BUILTIN_DANGEROUS_CALLS.get(func.id)
    if not isinstance(func, _ast.Attribute) or not isinstance(func.value, _ast.Name):
        return None
    namespace = func.value.id
    if namespace == "builtins":
        return _BUILTIN_DANGEROUS_CALLS.get(func.attr)
    if namespace == "os":
        return _OS_DANGEROUS_CALLS.get(func.attr)
    if (namespace == "subprocess"
            and func.attr in _SUBPROCESS_DANGEROUS_CALLS
            and _subprocess_shell_truth(node) is True):
        return "subprocess shell=True"
    return None
def _visible_import_record(
    node: _ast.Call,
    imports: dict,
    lexical: LexicalScopeTable,
    scopes: dict[int, _ast.AST],
) -> tuple | None:
    func = node.func
    if isinstance(func, _ast.Name):
        name = func.id
    elif isinstance(func, _ast.Attribute) and isinstance(func.value, _ast.Name):
        name = func.value.id
    else:
        return None
    if call_head_is_shadowed(node, lexical, scopes):
        return None
    scope = scopes.get(id(node))
    direct = scope
    while scope is not None:
        if not (isinstance(scope, _ast.ClassDef) and scope is not direct):
            record = imports.get(scope, {}).get(name)
            if record is not None:
                return record
        scope = lexical.parent.get(scope)
    return None

def _canonical_import_bound_call(
    node: _ast.Call,
    imports: dict,
    lexical: LexicalScopeTable,
    scopes: dict[int, _ast.AST],
) -> str:
    record = _visible_import_record(node, imports, lexical, scopes)
    if record is None:
        return ""
    func = node.func
    if record[0] == "import" and isinstance(func, _ast.Attribute):
        return f"{record[1]}.{func.attr}"
    if record[0] == "from" and record[1] and isinstance(func, _ast.Name):
        return f"{record[1]}.{record[2]}"
    return ""

def _describe_import_bound_dangerous_call(
    node: _ast.Call,
    imports: dict,
    lexical: LexicalScopeTable,
    scopes: dict[int, _ast.AST],
) -> str | None:
    canonical = _canonical_import_bound_call(node, imports, lexical, scopes)
    if canonical == "builtins.eval":
        return "eval()"
    if canonical == "builtins.exec":
        return "exec()"
    if canonical == "os.system":
        return "os.system()"
    if canonical == "os.popen":
        return "os.popen()"
    namespace, _separator, member = canonical.rpartition(".")
    if (namespace == "subprocess"
            and member in _SUBPROCESS_DANGEROUS_CALLS
            and _subprocess_shell_truth(node) is True):
        return "subprocess shell=True"
    return None

def _ast_danger_hits(content: str) -> dict[str, dict[str, int]] | None:
    try:
        tree = _ast.parse(content)
    except PARSE_DEGRADE_EXC as exc:
        _log.debug("危险调用 AST 边界不可判定，降级保守扫描: %s", exc)
        return None
    imports = scope_import_tables(tree)
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    lines = content.splitlines()
    hits: dict[str, dict[str, int]] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, _ast.Call):
            continue
        desc = _describe_dangerous_call(node)
        if desc is None:
            desc = _describe_import_bound_dangerous_call(
                node, imports, lexical, scopes)
        if desc is None:
            continue
        key = lines[node.lineno - 1].strip()
        desc_hits = hits.setdefault(desc, {})
        desc_hits[key] = desc_hits.get(key, 0) + 1
    return hits
def _danger_hits(content: str | None) -> dict[str, dict[str, int]]:
    text = content or ""
    parsed = _ast_danger_hits(text)
    if parsed is None:
        spans = _danger_spans(content)
        parsed = {
            desc: _danger_line_hits(pattern, content, spans)
            for pattern, desc in _DANGEROUS_FUNCTION_PATTERNS
        }
    return {
        desc: parsed.get(desc, {})
        for _pattern, desc in _DANGEROUS_FUNCTION_PATTERNS
    }
def _added_danger_hits(content: str,
                       existing_content: str | None
                       ) -> dict[str, dict[str, int]]:
    existing = _danger_hits(existing_content)
    added: dict[str, dict[str, int]] = {}
    for desc, current_hits in _danger_hits(content).items():
        existing_hits = existing.get(desc, {})
        desc_added: dict[str, int] = {}
        for key, count in current_hits.items():
            delta = count - existing_hits.get(key, 0)
            if delta > 0:
                desc_added[key] = delta
        if desc_added:
            added[desc] = desc_added
    return added
def _enforce_danger_patterns(content: str, filepath: str,
                             existing_content: str | None,
                             strict: bool) -> None:
    for desc in _added_danger_hits(content, existing_content):
        msg = f"Security violation in content: {desc}"
        safe_write_audit("guarded_write_danger_blocked", path=filepath,
                         pattern=desc, blocked=strict)
        if strict:
            raise ContractViolationError(msg)
        _log.warning("guarded_write: %s in %s", desc, filepath)
_REPLACE_MAX_ATTEMPTS = 6
_REPLACE_RETRY_BACKOFF = 0.01
def replace_with_retry(src: str, dst: str) -> None:
    for attempt in range(_REPLACE_MAX_ATTEMPTS):
        try:
            os.replace(src, dst)
            return
        except PermissionError:
            if attempt == _REPLACE_MAX_ATTEMPTS - 1:
                raise
            _time.sleep(_REPLACE_RETRY_BACKOFF * (attempt + 1))
def _cleanup_failed_fdopen(tmp_fd: int, tmp_path: str, filepath: str,
                          fdopen_err: BaseException) -> None:
    safe_write_audit("guarded_write_failed", path=filepath,
                     stage="fdopen",
                     error=f"{type(fdopen_err).__name__}: {fdopen_err}")
    try:
        os.close(tmp_fd)
    except OSError as _close_err:
        if getattr(_close_err, "errno", None) != errno.EBADF:
            _log.warning("guarded_write: 临时 fd 关闭失败: %s", _close_err)
    _cleanup_tmp_artifact(
        tmp_path, "guarded_write: 影子临时文件", warn=True)
def _normalized_for_text_stream(content: str, newline: str | None) -> str:
    if newline in (None, "\r", "\r\n"):
        return content.replace("\r\n", "\n").replace("\r", "\n")
    return content
def _text_stream_newline(newline: str | None) -> str:
    return "\n" if newline is None else newline
def _serialized_text_for_compare(content: str, newline: str | None) -> str:
    normalized = _normalized_for_text_stream(content, newline)
    if newline in ("\r", "\r\n"):
        return normalized.replace("\n", newline)
    return normalized
def _atomic_write_content(content: str, filepath: str, dirpath: str,
                          encoding: str, newline: str | None,
                          exclusive: bool = False,
                          prefix: str = ".guarded_write_tmp_",
                          suffix: str | None = None) -> None:
    if exclusive:
        # ``open(..., 'x')`` 等价于 O_CREAT|O_EXCL，但不暴露裸 fd，
        # 避免「os.open 后转交 fdopen」的所有权转移被静态分析误判为泄漏。
        tmp_path = filepath
        _f = open(filepath, "x", encoding=encoding,
                  newline=_text_stream_newline(newline))
    else:
        tmp_fd, tmp_path = _tempfile.mkstemp(
            dir=dirpath or ".",
            prefix=prefix,
            suffix=(os.path.basename(filepath) if suffix is None else suffix),
        )
        try:
            _f = os.fdopen(tmp_fd, "w", encoding=encoding,
                           newline=_text_stream_newline(newline))
        except BaseException as _fdopen_err:
            _cleanup_failed_fdopen(tmp_fd, tmp_path, filepath, _fdopen_err)
            raise
    try:
        with _f:
            _f.write(_normalized_for_text_stream(content, newline))
            _f.flush()
            os.fsync(_f.fileno())
        if not exclusive:
            _align_replaced_mode(tmp_path, filepath)
            replace_with_retry(tmp_path, filepath)
    except BaseException as _write_err:
        safe_write_audit("guarded_write_failed", path=filepath,
                         stage="write",
                         error=f"{type(_write_err).__name__}: {_write_err}")
        _cleanup_tmp_artifact(
            tmp_path, "guarded_write: 影子临时文件", warn=True)
        raise
SKILL_DOC_FILENAME = "SKILL.md"
def _prepare_write_target(filepath: str) -> tuple[str, str, str]:
    filepath = os.path.abspath(filepath)
    return (filepath, os.path.dirname(filepath),
            _strip_tmp_suffix(filepath))
def _pre_write_checks(content: str, filepath: str, semantic_fp: str,
                      encoding: str, strict: bool) -> str | None:
    existing_content = _read_existing_text(filepath, encoding, strict=False)
    if _is_python_source(semantic_fp):
        _enforce_danger_patterns(content, filepath, existing_content, strict)
    if (semantic_fp.lower().endswith(".md")
            and os.path.basename(semantic_fp).lower()
            == SKILL_DOC_FILENAME.lower()):
        _check_md_frontmatter_name(content, filepath)
    return existing_content
class _GuardedWriteRequest(NamedTuple):
    content: str
    filepath: str
    dirpath: str
    semantic_fp: str
    encoding: str
    newline: str | None
    preserve_form: bool
    exclusive: bool
def _logical_form_text(text: str) -> str:
    return text.replace("\r\n", "\n").replace("\r", "\n")
def _commit_guarded_write(request: _GuardedWriteRequest,
                          existing_content: str | None) -> None:
    if request.dirpath and not os.path.isdir(request.dirpath):
        os.makedirs(request.dirpath, exist_ok=True)
    if request.exclusive and os.path.lexists(request.filepath):
        raise FileExistsError(
            errno.EEXIST, os.strerror(errno.EEXIST), request.filepath)
    unchanged = existing_content is not None and (
        _logical_form_text(existing_content) == _logical_form_text(request.content)
        if request.preserve_form
        else existing_content == _serialized_text_for_compare(
            request.content, request.newline))
    if unchanged:
        _log.debug("guarded_write: 内容未变更，跳过写入 %s", request.filepath)
        return
    if os.path.isfile(request.filepath):
        _backup_before_write(request.filepath)
    _atomic_write_content(
        request.content, request.filepath, request.dirpath,
        request.encoding, request.newline, request.exclusive)
    if _is_python_source(request.semantic_fp):
        check_s02_portal_file(request.filepath, request.encoding)
def _form_lines(text: str) -> tuple[list[str], list[str]]:
    bodies: list[str] = []
    eols: list[str] = []
    for segment in split_tokenizer_lines(text):
        body = segment.rstrip("\r\n")
        bodies.append(body)
        eols.append(segment[len(body):])
    return bodies, eols
def _following_eol(eols: Sequence[str | None], start: int,
                  default_eol: str) -> str:
    return next((eol for eol in eols[start:] if eol), default_eol)
def _inherit_eols(new_lines: list[str], old_lines: list[str],
                  old_eols: list[str], default_eol: str) -> list[str]:
    resolved: list[str | None] = [None] * len(new_lines)
    matcher = difflib.SequenceMatcher(a=old_lines, b=new_lines, autojunk=False)
    for tag, i1, _i2, j1, j2 in matcher.get_opcodes():
        if tag != "equal":
            continue
        for offset in range(j2 - j1):
            resolved[j1 + offset] = old_eols[i1 + offset]
    head = 0
    while head < len(resolved) and resolved[head] is None:
        head += 1
    if head:
        following = _following_eol(resolved, head, default_eol)
        for index in range(head):
            resolved[index] = following
    previous = default_eol
    for index, eol in enumerate(resolved):
        if eol is None:
            resolved[index] = previous
        elif eol:
            previous = eol
    return [eol if eol is not None else default_eol for eol in resolved]
def _normalize_eols(eols: list[str], trailing: bool,
                    default_eol: str) -> list[str]:
    normalized = list(eols)
    for index, eol in enumerate(normalized):
        if eol or (index == len(normalized) - 1 and not trailing):
            continue
        normalized[index] = _following_eol(
            normalized, index + 1, default_eol)
    if normalized:
        normalized[-1] = normalized[-1] if trailing else ""
    return normalized
def _restore_existing_form(content: str, filepath: str,
                           encoding: str) -> tuple[str, str]:
    if not os.path.isfile(filepath):
        return content, encoding
    try:
        with open(filepath, "rb") as raw_file:
            raw = raw_file.read()
        has_utf8_bom = raw.startswith(_UTF8_BOM_BYTES)
        old_text = raw.decode(_UTF8_SIG_ENCODING if has_utf8_bom
                              else encoding)
    except (OSError, UnicodeDecodeError) as exc:
        log_swallowed(__name__, exc,
                      context=f"_restore_existing_form:{type(exc).__name__}")
        return content, encoding
    if has_utf8_bom:
        content = content.removeprefix("\ufeff")
    new_bodies = _logical_form_text(content).split("\n")
    trailing = bool(new_bodies) and new_bodies[-1] == ""
    if trailing:
        new_bodies.pop()
    old_bodies, old_eols = _form_lines(old_text)
    default_eol = detect_newline(old_text)
    eols = _inherit_eols(new_bodies, old_bodies, old_eols, default_eol)
    eols = _normalize_eols(eols, trailing, default_eol)
    adapted = "".join(line + eols[index] for index, line in enumerate(new_bodies))
    write_encoding = _UTF8_SIG_ENCODING if has_utf8_bom else encoding
    return adapted, write_encoding
def guarded_write(content: str, filepath: str, strict: bool = _DEFAULT_GUARDED_WRITE_STRICT, encoding: str = _DEFAULT_TEXT_ENCODING,
                  newline: str | None = None, preserve_form: bool = False,
                  exclusive: bool = False) -> None:
    filepath, dirpath, semantic_fp = _prepare_write_target(filepath)
    _enforce_diagnosis_readonly(semantic_fp, filepath)
    if preserve_form:
        content, encoding = _restore_existing_form(content, filepath, encoding)
        newline = ""
    existing_content = _pre_write_checks(
        content, filepath, semantic_fp, encoding, strict)
    request = _GuardedWriteRequest(
        content, filepath, dirpath, semantic_fp, encoding, newline,
        preserve_form, exclusive)
    _commit_guarded_write(request, existing_content)
def _check_md_frontmatter_name(content: str, filepath: str) -> None:
    _stripped = content.lstrip("\ufeff").strip()
    if not _stripped.startswith("---"):
        return
    _fm_end = _stripped.find("\n---", 3)
    if _fm_end > 0 and not re.search(r"(?m)^name[ \t]*:", _stripped[3:_fm_end]):
        _log.warning("guarded_write: SKILL.md 缺少 name 字段: %s", filepath)
_GUARDED_APPEND_LOCK = threading.Lock()
class _GuardedFileWriter:
    def __init__(self, filepath: str, encoding: str, newline: str | None,
                 strict: bool, append: bool, preserve_form: bool,
                 exclusive: bool):
        self._filepath = filepath
        self._encoding = encoding
        self._newline = newline
        self._strict = strict
        self._buffer = []
        self._append = append
        self._preserve_form = preserve_form
        self._exclusive = exclusive
        self._closed = False
    def write(self, text):
        if self._closed:
            raise ValueError("I/O operation on closed file.")
        self._buffer.append(text)
        return len(text)
    def writelines(self, lines):
        for line in lines:
            self.write(line)
    def flush(self):  # jwsgj:suppress empty_function
        pass
    def fileno(self):
        raise OSError("guarded_open does not support fileno() -- buffered writer")
    def close(self):
        if self._closed:
            return
        content = "".join(self._buffer)
        try:
            lock_context = (_GUARDED_APPEND_LOCK if self._append
                            else _contextlib.nullcontext())
            with lock_context:
                artifact_lock = (locked_artifact(self._filepath)
                                 if self._append else _contextlib.nullcontext(True))
                with artifact_lock as locked:
                    if not locked:
                        raise OSError(
                            "guarded_open 追加模式无法取得跨进程锁，"
                            f"已阻断写入以保护原内容: {self._filepath}")
                    if self._append:
                        content = (_read_existing_text(
                            self._filepath, self._encoding, strict=True) or "") + content
                    guarded_write(content, self._filepath, strict=self._strict,
                                  encoding=self._encoding, newline=self._newline,
                                  preserve_form=self._preserve_form,
                                  exclusive=self._exclusive)
        finally:
            self._closed = True
            self._buffer = []
    def __enter__(self):
        return self
    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self.close()
        else:
            self._closed = True
            self._buffer = []
        return False
_DIAG_READONLY_ROOT: _contextvars.ContextVar[str | None] = _contextvars.ContextVar(
    "jwsgj_diag_readonly_root", default=None)
_DIAG_READONLY_VIOLATIONS: list[dict] = []
_DIAG_READONLY_LOCK = threading.Lock()
def diagnosis_readonly_scope(skill_dir: str):
    root_text = fs_path_text(skill_dir)
    if not root_text.strip():
        root = ""
    else:
        try:
            root = os.path.normcase(
                os.path.realpath(os.path.abspath(root_text)))
        except (OSError, ValueError, TypeError):
            root = ""
    return _diagnosis_readonly_cm(root)
@_contextlib.contextmanager
def _diagnosis_readonly_cm(root: str):
    token = _DIAG_READONLY_ROOT.set(root)
    try:
        yield
    finally:
        _DIAG_READONLY_ROOT.reset(token)
def _diagnosis_readonly_violation(filepath: str) -> str:
    root = _DIAG_READONLY_ROOT.get()
    if root is None:
        return ""
    text = os.fspath(filepath) if isinstance(filepath, (str, os.PathLike)) else ""
    if not isinstance(text, str) or not text.lower().endswith(".py"):
        return ""
    if not root:
        return (f"诊断只读契约：技能根为空或不可解析，拒绝写源码 {text!r}。"
                "请先提供有效的被治理技能根，不能用进程 cwd 代替。")
    try:
        real = os.path.normcase(os.path.realpath(os.path.abspath(text)))
    except (OSError, ValueError, TypeError):
        return ""
    try:
        if os.path.commonpath([real, root]) != root:
            return ""
    except (OSError, ValueError) as exc:
        return (f"诊断只读契约：无法确认路径边界，拒绝写源码 {text!r}"
                f"（技能根 {root!r}，边界错误 {type(exc).__name__}）。")
    return (f"诊断只读契约：拒绝写源码 {text!r}（技能根 {root!r}）。"
            "诊断阶段只产证据与报告，修复必须由治疗阶段执行。")
def _record_diag_readonly_violation(filepath: str, reason: str) -> None:
    entry = {"path": str(filepath)[:400], "reason": reason[:400],
             "ts": _time.strftime("%Y-%m-%dT%H:%M:%S")}
    with _DIAG_READONLY_LOCK:
        if len(_DIAG_READONLY_VIOLATIONS) < 200:
            _DIAG_READONLY_VIOLATIONS.append(entry)
    try:
        safe_write_audit("diag_readonly_violation", path=str(filepath)[:400],
                         reason=reason[:400])
    except Exception as _audit_exc:  # noqa: BLE001
        log_swallowed(__name__, _audit_exc, context="diag_readonly_violation")
def _enforce_diagnosis_readonly(semantic_path: str,
                                reported_path: str | None = None) -> None:
    reason = _diagnosis_readonly_violation(semantic_path)
    if not reason:
        return
    _record_diag_readonly_violation(
        reported_path if reported_path is not None else semantic_path, reason)
    _log.error("[guard_io] %s", reason)
    raise PermissionError(reason)
def get_diag_readonly_violations() -> list[dict]:
    with _DIAG_READONLY_LOCK:
        return [dict(item) for item in _DIAG_READONLY_VIOLATIONS]
def guarded_open(filepath: str, mode: str='w', encoding: str=_DEFAULT_TEXT_ENCODING, newline: str | None=None, strict: bool=_DEFAULT_GUARDED_WRITE_STRICT) -> _GuardedFileWriter:
    _validate_write_mode(mode)
    _enforce_diagnosis_readonly(filepath)
    writer_encoding = encoding or _DEFAULT_TEXT_ENCODING
    preserve_form = mode in _APPEND_MODES and newline is None
    return _GuardedFileWriter(filepath, encoding=writer_encoding,
                              newline=newline, strict=strict,
                              append=mode in _APPEND_MODES,
                              preserve_form=preserve_form,
                              exclusive=mode in _EXCLUSIVE_MODES)
_WRITE_MODES = frozenset({'w', 'wt', 'a', 'at', 'x', 'xt'})
_APPEND_MODES = frozenset({'a', 'at'})
_EXCLUSIVE_MODES = frozenset({'x', 'xt'})
def _validate_write_mode(mode: str) -> None:
    if mode in _WRITE_MODES:
        return
    raise ValueError(
        "guarded_open 仅支持写入模式 ('w', 'wt', 'a', 'at', 'x', 'xt')，"
        f"不支持: {mode!r}（读/二进制/更新模式请使用普通 open()）"
    )
def path_identity(path: str) -> str:
    """路径规范形式（委托 ``runtime_scope.canonical_path``，单一实现）。"""
    return canonical_path(path)
_BLANK_ROOT_REASON = "技能根为空，路径边界校验拒绝放行"
def _within_any_root(target_path: str, roots: list[str]) -> bool:
    target_text = fs_path_text(target_path)
    if not target_text.strip():
        return False
    real_path = path_identity(target_text)
    for root in roots:
        if not isinstance(root, str) or not root.strip():
            continue
        real_root = path_identity(root)
        try:
            if os.path.commonpath([real_path, real_root]) == real_root:
                return True
        except (ValueError, OSError) as exc:
            log_swallowed(__name__, exc,
                          context="_within_any_root:commonpath")
    return False
def _within_skill_root(skill_dir: str, target_path: str) -> bool:
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        return False
    return _within_any_root(target_path, [skill_dir])
def check_path_traversal(skill_dir: str, target_path: str) -> tuple[bool, str]:
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        return False, _BLANK_ROOT_REASON
    if not isinstance(target_path, str) or not target_path.strip():
        return False, "目标路径为空或类型非法，路径边界校验拒绝放行"
    try:
        full = (target_path if os.path.isabs(target_path)
                else os.path.join(skill_dir, target_path))
        if not _within_skill_root(skill_dir, full):
            return False, f"路径穿越检测: {target_path} 不在技能根目录 {skill_dir} 内"
        real_skill = path_identity(skill_dir)
        real_target = path_identity(full)
        if ".." in os.path.relpath(real_target, real_skill).split(os.sep):
            return False, f"路径包含 '..' 穿越: {target_path}"
        return True, "路径安全"
    except (OSError, ValueError, TypeError) as e:
        _log.error("check_path_traversal failed: %s", e, exc_info=True)
        return False, f"路径穿越检测异常: {e}"
def resolve_within_root(skill_dir: str, target_path: str) -> str | None:
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        return None
    if not isinstance(target_path, str) or not target_path.strip():
        return None
    try:
        full = (target_path if os.path.isabs(target_path)
                else os.path.join(skill_dir, target_path))
        if not _within_skill_root(skill_dir, full):
            return None
        return os.path.realpath(full)
    except (OSError, ValueError, TypeError) as e:
        log_swallowed(__name__, e, context='resolve_within_root')
        return None
def _require_path_arg(value, arg_name: str) -> str:
    if not isinstance(value, (str, os.PathLike)):
        raise TypeError(
            f'{arg_name} 必须为 str 或 os.PathLike，收到 '
            f'{type(value).__name__}: {value!r}')
    _norm = os.fspath(value)
    if not isinstance(_norm, str):
        raise TypeError(
            f'{arg_name} 的 __fspath__ 必须返回 str，收到 '
            f'{type(_norm).__name__}')
    return _norm
def _require_nonblank_root(skill_dir) -> str:
    root = _require_path_arg(skill_dir, 'skill_dir')
    if not root.strip():
        raise ValueError('skill_dir 不能为空：空技能根使路径穿越与边界校验失效')
    return root
def _sandbox_segments(rel_path: str) -> tuple[list[str], list[str]]:
    segments = [p for p in rel_path.replace('\\', '/').split('/') if p]
    resolved: list[str] = []
    for part in segments:
        if part == '.':
            continue
        if part != '..':
            resolved.append(part)
        elif resolved and resolved[-1] != '..':
            resolved.pop()
        else:
            resolved.append(part)
    return segments, resolved
def sandbox_path(skill_dir: str, rel_path: str) -> str:
    skill_dir = _require_nonblank_root(skill_dir)
    rel_path = _require_path_arg(rel_path, 'rel_path')
    if (rel_path.startswith(("/", "\\"))
            or re.match(r"^[A-Za-z]:", rel_path)):
        raise ValueError(
            f'rel_path 必须是相对路径，禁止绝对/驱动器路径: {rel_path!r}')
    segments, parts = _sandbox_segments(rel_path)
    if parts != segments:
        _log.warning(
            "sandbox_path: 相对路径含 '.'/'..' 段，已按路径语义归一: %s -> %s",
            rel_path, '/'.join(parts))
    result = os.path.join(skill_dir, *parts)
    safe, _ = check_path_traversal(skill_dir, result)
    if not safe:
        raise ValueError(f'路径穿越被阻止: {rel_path} -> {result}')
    return result
_SKILL_ROOT_MAX_DEPTH = 8
def resolve_skill_dir(md_path: Any,
                      *, max_depth: int = _SKILL_ROOT_MAX_DEPTH) -> str:
    text = normalize_path_arg(md_path)
    if not isinstance(text, str) or not text.strip():
        return ""
    try:
        path = _Path(os.path.abspath(text.strip()))
        is_dir = path.is_dir()
    except (OSError, ValueError, TypeError) as _e:
        log_swallowed(__name__, _e, context='resolve_skill_dir:path')
        return ""
    fallback = path if is_dir else path.parent
    current = fallback
    depth = (max(1, max_depth)
             if isinstance(max_depth, int) and not isinstance(max_depth, bool)
             else _SKILL_ROOT_MAX_DEPTH)
    for _ in range(depth):
        try:
            if (current / SKILL_DOC_FILENAME).is_file():
                return str(current)
        except (OSError, ValueError) as _e:
            log_swallowed(__name__, _e, context='resolve_skill_dir:probe')
            break
        parent = current.parent
        if parent == current:
            break
        current = parent
    return str(fallback)
def validate_skill_boundary(skill_dir: str, file_path: str) -> tuple[bool, str]:
    skill_dir = _require_nonblank_root(skill_dir)
    file_path = _require_path_arg(file_path, 'file_path')
    if not file_path.strip():
        raise ValueError('file_path 不能为空：空路径被解析为进程 cwd 会产生误放行')
    root = _Path(skill_dir)
    candidate = _Path(file_path)
    if not candidate.is_absolute():
        candidate = root / candidate
    sp = root.resolve()
    fp = candidate.resolve()
    safe, reason = check_path_traversal(str(sp), str(fp))
    if not safe:
        return (False, reason)
    return (True, '在技能边界内')
def normalize_path_arg(value: Any) -> Any:
    if isinstance(value, os.PathLike):
        try:
            return os.fsdecode(os.fspath(value))
        except (TypeError, ValueError, OSError) as _e:
            log_swallowed(
                __name__, _e,
                context=f'normalize_path_arg:{type(_e).__name__}')
    return value
def normalize_out_path(value: Any) -> str | None:
    text = normalize_path_arg(value)
    if not isinstance(text, str):
        return None
    return text.strip() or None
def coerce_target_file(value: Any) -> str:
    return normalize_out_path(value) or ""
def fs_path_text(value: Any) -> str:
    try:
        return os.fsdecode(os.fspath(value))
    except (TypeError, ValueError, OSError) as _e:
        log_swallowed(__name__, _e,
                      context=f'fs_path_text:{type(_e).__name__}')
        return ""
_FO_DELETE = 0x0003
_FOF_ALLOWUNDO = 0x0040
_FOF_NOCONFIRMATION = 0x0010
_FOF_SILENT = 0x0004
SHFILEOP_TIMEOUT_S = 5.0
_SHFILEOP_GRACE_S = 1.0
try:
    import ctypes as _ctypes
    from ctypes import wintypes as _wintypes
except ImportError as _e:
    _log.debug("ctypes 导入失败(回收站降级不可用): %s", _e)
    _ctypes = None
    _wintypes = None
if _ctypes is not None and _wintypes is not None:
    class _SHFILEOPSTRUCT(_ctypes.Structure):  # type: ignore[valid-type,misc]
        _fields_ = [  # noqa: RUF012
            ("hwnd", _wintypes.HWND),
            ("wFunc", _wintypes.UINT),
            ("pFrom", _wintypes.LPCWSTR),
            ("pTo", _wintypes.LPCWSTR),
            ("fFlags", _wintypes.WORD),
            ("fAnyOperationsAborted", _wintypes.BOOL),
            ("hNameMappings", _wintypes.LPVOID),
            ("lpszProgressTitle", _wintypes.LPCWSTR),
        ]
else:
    _SHFILEOPSTRUCT = None
def _recycle_dependencies_ready() -> bool:
    return (_ctypes is not None and _wintypes is not None
            and _SHFILEOPSTRUCT is not None
            and hasattr(_ctypes, "windll"))
def _invoke_shfileop_watched(abs_path: str) -> tuple[threading.Thread, dict[str, Any]]:
    shell32 = _ctypes.windll.shell32
    shfileop = shell32.SHFileOperationW
    shfileop.argtypes = [_ctypes.POINTER(_SHFILEOPSTRUCT)]
    shfileop.restype = _wintypes.INT
    from_path = abs_path + "\0"
    op = _SHFILEOPSTRUCT()
    op.wFunc = _FO_DELETE
    op.pFrom = from_path
    op.fFlags = _FOF_ALLOWUNDO | _FOF_NOCONFIRMATION | _FOF_SILENT
    outcome: dict[str, Any] = {}
    def _worker_invoke() -> None:
        try:
            outcome["result"] = shfileop(_ctypes.byref(op))
        except BaseException as _be:  # noqa: BLE001
            _log.debug('静默降级[move_to_recycle_bin._worker_invoke:BaseExc]: %s: %s', type(_be).__name__, _be)
            outcome["error"] = _be
    worker = threading.Thread(target=_worker_invoke, daemon=True)
    worker.start()
    worker.join(SHFILEOP_TIMEOUT_S)
    return worker, outcome
def _wait_target_gone(abs_path: str, grace: float) -> bool:
    deadline = _time.monotonic() + max(0.0, grace)
    while os.path.lexists(abs_path):
        if _time.monotonic() >= deadline:
            return False
        _time.sleep(0.05)
    return True
def _classify_shfileop_result(result: Any, abs_path: str) -> bool:
    target_gone = not os.path.lexists(abs_path)
    if result in (0, 2) and target_gone:
        return True
    if result == 0:
        _log.error(
            "SHFileOperationW reported success but target still exists: %s",
            abs_path)
    else:
        _log.error("SHFileOperationW failed with code %s for path: %s",
                   result, abs_path)
    return False
def move_to_recycle_bin(path: str) -> bool:
    if not os.path.lexists(path):
        return True
    if not _recycle_dependencies_ready():
        _log.error(
            "回收站删除通道仅在 Windows 平台可用（Shell API 依赖 ctypes）: %s",
            path)
        return False
    try:
        abs_path = os.path.abspath(path)
        worker, outcome = _invoke_shfileop_watched(abs_path)
        if worker.is_alive():
            if _wait_target_gone(abs_path, _SHFILEOP_GRACE_S):
                _log.warning(
                    "SHFileOperationW 响应超过 %.1fs，目标已移入回收站: %s",
                    SHFILEOP_TIMEOUT_S, abs_path)
                return True
            _log.error(
                "SHFileOperationW 阻塞超时（>%.1fs，回收站通道不可用）: %s",
                SHFILEOP_TIMEOUT_S, abs_path)
            return False
        if "error" in outcome:
            raise outcome["error"]
        return _classify_shfileop_result(outcome.get("result"), abs_path)
    except Exception:  # noqa: BLE001
        _log.exception("回收站删除异常 %s", path)
        return False
def discard_tmp_file(tmp_path: str) -> None:
    _two_level_delete(tmp_path, os.unlink, 'discard_tmp_file')
def safe_delete(path: str) -> bool:
    if not os.path.lexists(path):
        return True
    ok = move_to_recycle_bin(path)
    safe_write_audit("guard_safe_delete", path=path, ok=ok)
    return ok
def _two_level_delete(path: str, direct: Callable[[str], None],
                      label: str) -> bool:
    try:
        direct(path)
        return True
    except FileNotFoundError as _e:
        log_swallowed(__name__, _e, context=f'{label}:FileNotFoundError')
        return True
    except OSError:
        if not os.path.lexists(path):
            return True
        _log.debug("直接删除失败，转入回收站通道: %s", path, exc_info=True)
    try:
        moved = move_to_recycle_bin(path)
    except OSError as _e:
        log_swallowed(__name__, _e,
                      context=f'{label}:RecycleBin:{type(_e).__name__}')
        return False
    if not moved:
        _log.debug("两级删除通道均失败（受限环境/占用）: %s", path)
    return moved
def two_level_unlink(path: str) -> bool:
    return _two_level_delete(path, os.remove, 'two_level_unlink')
def two_level_rmtree(path: str) -> bool:
    return _two_level_delete(path, _shutil.rmtree, 'two_level_rmtree')
_BUILTIN_CALL_LEFT = r"(?:(?<![\w.])|(?<=builtins\.))"
_BUILTIN_DANGEROUS_CALLS = {"eval": "eval()", "exec": "exec()"}
_OS_DANGEROUS_CALLS = {"system": "os.system()", "popen": "os.popen()"}
_SUBPROCESS_DANGEROUS_CALLS = frozenset({
    "Popen", "call", "run", "check_call", "check_output",
})
_SUBPROCESS_SHELL_TRUTHY_RE = (
    r"(?:True|[+-]?[1-9]\d*|[bB]?['\"][^'\"\r\n]+['\"])"
)
_DANGEROUS_FUNCTION_PATTERNS = [
    (re.compile(_BUILTIN_CALL_LEFT + r'eval\s*\(', re.IGNORECASE),
     "eval()"),
    (re.compile(_BUILTIN_CALL_LEFT + r'exec\s*\(', re.IGNORECASE),
     "exec()"),
    (re.compile(r'(?<![\w.])os\.system\s*\(', re.IGNORECASE),
     "os.system()"),
    (re.compile(r'(?<![\w.])os\.popen\s*\(', re.IGNORECASE),
     "os.popen()"),
    (re.compile(
         r'(?<![\w.])subprocess\.'
         r'(?:Popen|call|run|check_call|check_output)\s*\('
         r'.{0,300}?shell\s*=\s*' + _SUBPROCESS_SHELL_TRUTHY_RE,
         re.IGNORECASE | re.DOTALL),
     "subprocess shell=True"),
]
def _line_offsets(text: str) -> list[int]:
    offsets = [0]
    for index, char in enumerate(text):
        if char == "\n":
            offsets.append(index + 1)
    return offsets
_STRING_LITERAL_TOKEN_TYPES = frozenset(
    {tokenize.STRING, tokenize.COMMENT}
    | {getattr(tokenize, _name) for _name in
       ("FSTRING_START", "FSTRING_MIDDLE", "FSTRING_END")
       if hasattr(tokenize, _name)}
)
def _literal_token_spans(text: str) -> list[tuple[int, int]] | None:
    try:
        tokens = list(tokenize.generate_tokens(io.StringIO(text).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        _log.debug("字面量边界分词失败(边界不可判定): %s", exc)
        return None
    offsets = _line_offsets(text)
    spans: list[tuple[int, int]] = []
    for tok in tokens:
        if tok.type not in _STRING_LITERAL_TOKEN_TYPES:
            continue
        start_row, start_col = tok.start
        end_row, end_col = tok.end
        spans.append((
            offsets[min(start_row - 1, len(offsets) - 1)] + start_col,
            offsets[min(end_row - 1, len(offsets) - 1)] + end_col,
        ))
    return spans
def _inside_any_span(position: int, spans: list[tuple[int, int]]) -> bool:
    return any(start <= position < end for start, end in spans)
def _is_python_source(filepath: Any) -> bool:
    return _strip_tmp_suffix(str(filepath or "").lower()).endswith(".py")
def _ensure_generated_py_import(content: str, filepath: str,
                               has_logs: bool) -> tuple[str, list[str]]:
    if not (has_logs and isinstance(filepath, str)
            and _is_python_source(filepath)
            and "os.environ.get" in content):
        return content, []
    patched = ensure_os_import(content)
    if patched == content:
        return content, []
    return patched, [f"已补齐: {filepath} (import os)"]
def atomic_write_text(file_path: str, content: str, tag: str = "atomic",
                      newline: str | None = None,
                      encoding: str = _DEFAULT_TEXT_ENCODING) -> None:
    target = os.path.abspath(file_path)
    _enforce_diagnosis_readonly(target)
    target_dir = os.path.dirname(target)
    safe_tag = _sanitize_backup_component(str(tag or "")) or "atomic"
    _atomic_write_content(
        content, target, target_dir, encoding, newline,
        prefix=f"._{safe_tag}_",
        suffix=f"_{os.path.basename(target)}.tmp",
    )
    _log.info("[file-write] %s 原子写盘完成 (tag=%s)", target, tag)
def write_text_atomic(path: str, text: str, *,
                       newline: str | None = None) -> None:
    target = os.path.abspath(path)
    _enforce_diagnosis_readonly(target)
    parent = os.path.dirname(target)
    if parent:
        os.makedirs(parent, exist_ok=True)
    atomic_write_text(target, text, newline=newline)
def safe_write_text(path: str, content: str, encoding: str = _DEFAULT_TEXT_ENCODING,
                    strict: bool = _DEFAULT_GUARDED_WRITE_STRICT) -> None:
    guarded_write(content, path, strict=strict, encoding=encoding, newline="\n")
def _unique_archive_path(dest_dir: str, stem: str) -> str:
    seq = 0
    while True:
        suffix = f"_{seq}" if seq else ""
        dest = os.path.join(dest_dir, f"{stem}{suffix}.bak")
        try:
            fd = os.open(
                dest, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o666)
        except FileExistsError:
            seq += 1
            continue
        os.close(fd)
        return dest
def archive_backup(file_path: str, skill_dir: str, tag: str) -> str:
    dest_dir = os.path.join(
        get_backup_base(os.path.abspath(skill_dir)), "code_feedback")
    safe_tag = _sanitize_backup_component(str(tag or "")) or "backup"
    stem = (f"{safe_tag}_{os.path.basename(file_path)}"
            f".{int(_time.time() * 1000)}_{os.getpid()}")
    dest = ""
    try:
        os.makedirs(dest_dir, exist_ok=True)
        dest = _unique_archive_path(dest_dir, stem)
        _shutil.copy2(file_path, dest)
    except OSError as e:
        _cleanup_tmp_artifact(dest, "[Backup] 失败归档")
        _log.warning("[Backup] 备份失败(%s): %s", tag, e)
        return ""
    except BaseException:
        _cleanup_tmp_artifact(dest, "[Backup] 失败归档")
        raise
    _log.info("[Backup] %s 已备份至 %s (tag=%s)", file_path, dest, tag)
    return dest
def detect_newline(text: str) -> str:
    if "\r\n" in text:
        return "\r\n"
    return "\r" if "\r" in text else "\n"
_TOKENIZER_LINE_RE = re.compile(r"[^\r\n]*(?:\r\n|\r|\n)|[^\r\n]+")
def split_tokenizer_lines(content: str) -> list[str]:
    return _TOKENIZER_LINE_RE.findall(content)
_BACKUP_NAME_UNSAFE_RE = re.compile(r'[\\/:*?"<>|\x00-\x1f]')
def _sanitize_backup_component(component: str) -> str:
    return _BACKUP_NAME_UNSAFE_RE.sub("_", component)
def _lock_file_name(stage: Any) -> str:
    safe = _sanitize_backup_component(str(stage or ""))
    return f"{safe or 'stage'}.lock"
def backup_file_name(modification_id: str, filepath: str,
                     seq: int | None = None) -> str:
    _seq = f"_{seq}" if seq is not None else ""
    return (f"{_sanitize_backup_component(modification_id)}{_seq}"
            f"_{os.path.basename(filepath)}.bak")
def sequenced_backup_path(
    backup_dir: str,
    modification_id: str,
    filepath: str,
    initial: str,
) -> str:
    candidate = initial
    dup = 2
    while os.path.exists(candidate):
        candidate = os.path.join(
            backup_dir, backup_file_name(modification_id, filepath, dup))
        dup += 1
    return candidate
def materialize_backup(filepath: str, backup_path: str) -> str:
    try:
        _backup_parent = os.path.dirname(backup_path)
        if _backup_parent and not os.path.isdir(_backup_parent):
            os.makedirs(_backup_parent, exist_ok=True)
        _shutil.copy2(filepath, backup_path)
    except OSError as e:
        _log.error("[Rollback] 备份创建失败(磁盘/权限)，快照降级为无备份: %s", e, exc_info=True)
        return ""
    try:
        os.utime(backup_path, None)
    except OSError:
        _log.debug("[Rollback] 备份 mtime 刷新失败（不影响备份可用性）: %s",
                   backup_path)
    return backup_path
def _collect_backup_mtimes(backup_dir: str) -> list[tuple[float, str]]:
    backups: list[tuple[float, str]] = []
    for f in os.listdir(backup_dir):
        if not f.casefold().endswith(".bak"):
            continue
        fpath = os.path.join(backup_dir, f)
        try:
            if not os.path.isfile(fpath):
                continue
            backups.append((os.path.getmtime(fpath), fpath))
        except OSError:
            _log.debug("[Rollback] 备份 mtime 读取失败(跳过): %s", fpath)
    return backups
def _delete_overflow_backups(overflow: list[tuple[float, str]],
                             exempt: set[str]) -> int:
    failed = 0
    for _, fpath in overflow:
        if path_identity(fpath) in exempt:
            continue
        if not safe_delete(fpath):
            failed += 1
            _log.warning("[Rollback] 备份删除失败(跳过继续): %s", fpath)
    return failed
def cleanup_backup_dir(
    backup_dir: str,
    max_backups: int,
    protect: set[str] | None = None,
) -> None:
    if isinstance(max_backups, bool) or not isinstance(max_backups, int):
        _log.warning(
            "[Rollback] cleanup_backup_dir: max_backups 非法(%r)，跳过清理",
            max_backups)
        return
    limit = max(0, max_backups)
    exempt = {path_identity(p) for p in (protect or ()) if p}
    try:
        backups = _collect_backup_mtimes(backup_dir)
        backups.sort(reverse=True)
        failed = _delete_overflow_backups(backups[limit:], exempt)
        if failed:
            _log.warning("[Rollback] 旧备份清理: %d 个删除失败", failed)
    except OSError:
        _log.warning(
            "[Rollback] cleanup_backup_dir: 旧备份清理失败", exc_info=True)
def _cleanup_tmp_artifact(tmp_path: str | None, label: str, *,
                         warn: bool = False) -> None:
    if (not tmp_path or not os.path.lexists(tmp_path)
            or os.path.isdir(tmp_path)):
        return
    try:
        removed = two_level_unlink(tmp_path)
    except OSError as exc:
        _log.debug("%s: 两级清理异常（残留待后续回收）: %s: %s",
                   label, tmp_path, exc)
        return
    if removed:
        return
    if warn:
        _log.warning("%s: 回收站清理失败（残留待后续回收）: %s",
                     label, tmp_path)
    else:
        _log.debug("%s: 回收站清理失败（残留待后续回收）: %s",
                   label, tmp_path)
def _fdopen_bytes(fd: int):
    try:
        return os.fdopen(fd, "wb")
    except BaseException:
        try:
            os.close(fd)
        except OSError:
            _log.debug(MSG_OSERROR_SUPPRESSED, exc_info=True)
        raise
def _align_replaced_mode(tmp_path: str, target_path: str) -> None:
    try:
        target_mode = os.stat(target_path).st_mode & 0o7777
    except FileNotFoundError:
        target_mode = _DEFAULT_FILE_MODE
    except OSError as exc:
        log_swallowed(__name__, exc,
                      context=f'_align_replaced_mode:{type(exc).__name__}')
        target_mode = _DEFAULT_FILE_MODE
    try:
        os.chmod(tmp_path, target_mode)
    except OSError:
        _log.debug(MSG_OSERROR_SUPPRESSED, exc_info=True)
def atomic_replace_bytes(target: str, payload: bytes, *, prefix: str,
                         label: str = "原子替换临时产物") -> None:
    _enforce_diagnosis_readonly(os.path.abspath(target))
    tmp_path: str | None = None
    try:
        safe_prefix = _sanitize_backup_component(str(prefix or "")) or "atomic_"
        fd, tmp_path = _tempfile.mkstemp(
            dir=os.path.dirname(target) or os.curdir,
            prefix=safe_prefix,
            suffix=os.path.splitext(target)[1],
        )
        with _fdopen_bytes(fd) as tmp_file:
            tmp_file.write(payload)
            tmp_file.flush()
            os.fsync(tmp_file.fileno())
        _align_replaced_mode(tmp_path, target)
        replace_with_retry(tmp_path, target)
    except BaseException:
        _cleanup_tmp_artifact(tmp_path, label)
        raise
def backup_path_for(bak_dir: str, file_path: str) -> str:
    tag = hashlib.sha1(
        os.path.realpath(os.path.abspath(file_path)).encode(
            _FINGERPRINT_ENCODING),
        usedforsecurity=False,
    ).hexdigest()[:8]
    return os.path.join(bak_dir, f"aifix_bak_{tag}_{os.path.basename(file_path)}")
def write_backup_bytes(skill_dir: str, file_path: str,
                       original_bytes: bytes | None) -> tuple[str, bool]:
    bak_dir = get_backup_base(skill_dir)
    backup_path = backup_path_for(bak_dir, file_path)
    try:
        os.makedirs(bak_dir, exist_ok=True)
        payload = original_bytes
        if payload is None:
            with open(file_path, "rb") as f:
                payload = f.read()
        atomic_replace_bytes(
            backup_path, payload,
            prefix=f".{os.path.basename(backup_path)}.tmp_",
            label="备份临时产物")
    except (OSError, ValueError) as exc:
        _log.warning("[Backup] 备份失败(%s): %s", type(exc).__name__, backup_path)
        return "", False
    return backup_path, True
_l2l3_write_verifier: Callable[..., bool] | None = None
def register_l2l3_write_verifier(verify_fn: Callable[..., bool] | None) -> None:
    global _l2l3_write_verifier
    _l2l3_write_verifier = verify_fn
def _verify_l1_syntax(
    filepath: str,
    details: dict[str, Any],
) -> tuple[bool, str | None, _ast.Module | None]:
    source, _l1_fp = read_source_with_fingerprint(filepath, strict=True)
    if source is None:
        details["error"] = f"文件读取失败: {filepath}"
        return False, None, None
    try:
        tree = _ast.parse(source)
    except PARSE_DEGRADE_EXC as e:
        log_swallowed(__name__, e,
                      context=f'verify_write_degradation:{type(e).__name__}')
        details["error"] = f"L1语法错误: {e}"
        return False, None, None
    details["L1_syntax"] = "passed"
    return True, source, tree
def _read_original_source(snapshot: Any) -> str | None:
    backup_path = getattr(snapshot, "backup_path", None)
    if not (backup_path and os.path.isfile(backup_path)):
        return None
    orig_source, _orig_fp = read_source_with_fingerprint(
        backup_path, strict=True)
    if orig_source is None:
        _log.warning(
            "[Rollback] verify_write_degradation: 原始源码读取失败: %s",
            snapshot.backup_path)
    return orig_source
_NODE_COUNT_RATIO_MIN = 0.7
_SIZE_RATIO_MIN = 0.5
def _verify_node_count(
    tree: _ast.Module,
    orig_source: str | None,
    details: dict[str, Any],
) -> bool:
    current_node_count = sum(1 for _ in walk_nodes(tree))
    details["current_node_count"] = current_node_count
    if orig_source is None:
        return True
    try:
        orig_tree = _ast.parse(orig_source)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'_verify_node_count:orig_tree:{type(_e).__name__}')
        _log.warning(
            "[Rollback] verify_write_degradation: 原始源码读取/解析失败", exc_info=True)
        details["error"] = f"原始源码语法解析失败，无法验证写后降级: {_e}"
        return False
    orig_node_count = sum(1 for _ in walk_nodes(orig_tree))
    details["original_node_count"] = orig_node_count
    if orig_node_count <= 0:
        return True
    ratio = current_node_count / orig_node_count
    details["node_ratio"] = round(ratio, 3)
    if ratio >= _NODE_COUNT_RATIO_MIN:
        return True
    details["error"] = (
        f"AST 节点数大幅减少: {orig_node_count} → {current_node_count} "
        f"(ratio={ratio:.2f}, 下限={_NODE_COUNT_RATIO_MIN:.2f})"
    )
    return False
def _verify_size_budget(
    filepath: str,
    snapshot: Any,
    details: dict[str, Any],
) -> bool:
    try:
        current_size = os.path.getsize(filepath)
    except OSError as e:
        log_swallowed(__name__, e,
                      context=f'_verify_size_budget:{type(e).__name__}')
        details["error"] = f"文件大小检查失败: {e}"
        return False
    original_size = getattr(snapshot, "size", 0)
    if isinstance(original_size, bool) or not isinstance(original_size, int):
        original_size = 0
    details["current_size"] = current_size
    details["original_size"] = original_size
    if original_size > 0:
        size_ratio = current_size / original_size
        details["size_ratio"] = round(size_ratio, 3)
        if size_ratio < _SIZE_RATIO_MIN:
            details["error"] = (
                f"文件大小异常缩小: {original_size} → {current_size} bytes "
                f"(ratio={size_ratio:.2f}, 下限={_SIZE_RATIO_MIN:.2f})"
            )
            return False
    return True
def verify_write_degradation(
    filepath: str,
    snapshot: Any,
    skill_dir: str,
) -> tuple[bool, dict[str, Any]]:
    details: dict[str, Any] = {}
    ok, source, tree = _verify_l1_syntax(filepath, details)
    if not ok:
        return False, details
    orig_source = _read_original_source(snapshot)
    backup_path = getattr(snapshot, "backup_path", None)
    original_exists = getattr(snapshot, "original_exists", True) is not False
    if orig_source is None and (original_exists or backup_path):
        baseline_ref = backup_path or "<backup_path 未生成>"
        details["error"] = (
            f"原始源码基线不可用，拒绝判定写后无降级: {baseline_ref}")
        return False, details
    l2l3 = _l2l3_write_verifier
    if orig_source is not None and l2l3 is not None:
        try:
            l2l3_result = l2l3(
                filepath, source, orig_source, skill_dir, details)
            if not isinstance(l2l3_result, bool):
                details["error"] = (
                    f"L2/L3 验证器返回形态异常({type(l2l3_result).__name__})，"
                    "按验证失败收口")
                return False, details
            l2l3_passed = l2l3_result
        except Exception as _l2l3_err:  # noqa: BLE001
            _log.warning("[Rollback] L2/L3 验证器执行异常（按失败关闭）",
                         exc_info=True)
            details["error"] = (
                f"L2/L3 验证器异常({type(_l2l3_err).__name__}): {_l2l3_err}")
            return False, details
        if not l2l3_passed:
            details.setdefault(
                "error", "L2/L3 安全验证未通过（验证器未给出原因）")
            return False, details
    if not _verify_node_count(tree, orig_source, details):
        return False, details
    if not _verify_size_budget(filepath, snapshot, details):
        return False, details
    details["error"] = ""
    return True, details
def _normalize_verify_fn_result(ver: Any) -> tuple[bool, dict[str, Any]]:
    if isinstance(ver, bool):
        return ver, {}
    if (not isinstance(ver, tuple) or len(ver) != 2
            or not isinstance(ver[0], bool)):
        return False, {"error": (
            f"verify_fn 返回形态异常({type(ver).__name__})，"
            f"按验证失败收口")}
    passed = ver[0]
    raw_details = ver[1]
    if isinstance(raw_details, dict):
        return passed, raw_details
    if raw_details is None:
        return passed, {}
    return passed, {"detail" if passed else "error": str(raw_details)}
def run_verify_guarded(
    verify_fn: Any | None,
    default_verify: Any,
    filepath: str,
    snapshot: Any,
) -> tuple[bool, dict[str, Any]]:
    if verify_fn is not None:
        try:
            return _normalize_verify_fn_result(verify_fn(filepath))
        except Exception as e:  # noqa: BLE001
            _log.warning("[Rollback] verify_fn 执行异常", exc_info=True)
            return False, {"error": str(e)}
    try:
        return _normalize_verify_fn_result(default_verify(filepath, snapshot))
    except Exception as e:  # noqa: BLE001
        _log.warning("[Rollback] 默认验证执行异常", exc_info=True)
        return False, {"error": f"验证执行异常: {e}"}
def verify_syntax(file_path: str, tag: str = "") -> bool:
    try:
        with tokenize.open(file_path) as f:
            source = f.read()
        compile(source, file_path, "exec")
        return True
    except (UnicodeDecodeError, OSError) as e:
        _log.warning("%s 语法检查读取失败 %s: %s", tag, file_path, e)
        return False
    except PARSE_DEGRADE_EXC as e:
        _log.error("%s 语法验证失败 %s: %s (line %s)",
                     tag, file_path, getattr(e, "msg", e),
                     getattr(e, "lineno", None), exc_info=True)
        return False
def compile_error(source: str, filename: str, tag: str = "") -> str:
    try:
        compile(source, filename, "exec")
    except PARSE_DEGRADE_EXC as e:
        _log.debug("[%s] 语法校验失败: %s", tag or "compile", e, exc_info=True)
        return str(e)[:200]
    return ""
def read_text_bom(path: str) -> str | None:
    try:
        with tokenize.open(path) as f:
            return f.read()
    except (OSError, UnicodeDecodeError, SyntaxError):
        _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
        return None
class SourceReadError(ValueError):
    pass
def detect_source_encoding(raw: bytes) -> str:
    try:
        encoding, _lines = tokenize.detect_encoding(io.BytesIO(raw).readline)
    except (SyntaxError, UnicodeDecodeError, LookupError) as exc:
        log_swallowed(__name__, exc, context='detect_source_encoding')
        return _DEFAULT_TEXT_ENCODING
    return encoding or _DEFAULT_TEXT_ENCODING
def decode_source_strict(raw: bytes) -> tuple[str, str]:
    try:
        encoding, _lines = tokenize.detect_encoding(io.BytesIO(raw).readline)
    except (SyntaxError, UnicodeDecodeError, LookupError) as exc:
        raise SourceReadError(
            f"源文件编码声明无法解析({type(exc).__name__})，"
            f"为避免写盘破坏原文件已拒绝修复") from exc
    encoding = encoding or _DEFAULT_TEXT_ENCODING
    try:
        return raw.decode(encoding), encoding
    except (UnicodeDecodeError, LookupError) as exc:
        raise SourceReadError(
            f"源文件无法按 {encoding} 编码解码({type(exc).__name__})，"
            f"为避免写盘破坏原文件已拒绝修复") from exc
def read_source_text_strict(path: str) -> str:
    with open(path, "rb") as f:
        raw = f.read()
    return decode_source_strict(raw)[0]
def bytes_fingerprint(data: bytes) -> str:
    return hashlib.md5(data, usedforsecurity=False).hexdigest()
def content_fingerprint(text: str) -> str:
    return bytes_fingerprint(text.encode(_FINGERPRINT_ENCODING))
def normalize_fs_key(path: str) -> str:
    return os.path.normcase(os.path.abspath(path))
def format_diff_preview(before_lines: list[str] | tuple,
                        after_lines: list[str] | tuple,
                        file_label: str) -> str:
    return "\n".join(difflib.unified_diff(
        before_lines, after_lines,
        fromfile=file_label, tofile=file_label, lineterm=""))

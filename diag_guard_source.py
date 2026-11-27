from __future__ import annotations

import ast
import bisect
import io
import logging
import os
import re
import tokenize
from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_shared_source_core import (
    ast_split_lines,
    count_lines,
    parse_cached,
    read_source_interpreter_encoding,
)
from jwsgj.diag_types_defs import (
    GuardResult,
    OperationContext,
    code_to_write_str,
    is_read_only_audit,
    issues_guard_result,
    target_path_str,
)
from jwsgj.diag_types_normalize import normalize_files_list
from jwsgj.diag_types_vocab import GuardLevel, OperationType
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import (
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    TEST_ARTIFACT_DIRS,
    is_audit_skip_dir,
    is_backup_like_dir,
    is_py_source_file,
    is_runtime_temp_path,
    is_test_file_path,
)

_log = logging.getLogger(__name__)
_VIRTUAL_PENDING_TARGET = "<code_to_write>"
__all__ = [
    'DEFAULT_MAX_FILE_COUNT',
    'DEFAULT_MAX_FILE_SIZE',
    'DEFAULT_MAX_LINES',
    'DEFAULT_MAX_TOTAL_SIZE',
    'content_label',
    'find_unclosed_triple_quotes',
    'guard_content_diag',
    'guard_docstring',
    'guard_fstring',
    'guard_size_limit',
    'guard_syntax',
    'iter_scan_sources',
    'iter_scan_sources_with_ast',
    'parse_safe',
    'resolve_guard_scan_targets',
    'scan_content_dangerous',
]
_log.info("diag_guard_source 已加载：%d 项导出", len(__all__))
def parse_safe(source: str | ast.Module) -> ast.Module | None:
    if isinstance(source, ast.Module):
        return source
    try:
        return parse_cached(source)
    except (SyntaxError, TypeError, ValueError, AttributeError,
            RecursionError, MemoryError) as e:
        _log.warning("[GuardQuality] AST解析失败(返回None): %s", e)
        return None
def _cache_lookup(ctx: OperationContext, fpath: str) -> tuple[Any, str | None]:
    _sc = ctx.metadata.get('shared_cache')
    if _sc is None:
        return None, None
    try:
        src = _sc.get_source(fpath)
    except Exception:  # noqa: BLE001 — 鸭子类型缓存对象异常类型不可枚举
        _log.debug("[GuardQuality] SharedCache get_source 降级直读: %s",
                   fpath, exc_info=True)
        return _sc, None
    if src is None:
        return _sc, None
    if not isinstance(src, str):
        _log.warning(
            "[GuardQuality] SharedCache get_source 返回形态违约"
            "（期望 str|None，实际 %s），降级直读: %s",
            type(src).__name__, fpath)
        return _sc, None
    if '\ufffd' in src:
        return _sc, None
    return _sc, src
def _read_source_cached(ctx: OperationContext, fpath: str) -> str:
    _cache, src = _cache_lookup(ctx, fpath)
    if src is not None:
        return src
    return read_source_interpreter_encoding(fpath)
def _read_source_and_ast_cached(ctx: OperationContext, fpath: str) -> tuple[str | None, ast.Module | None]:
    _sc = ctx.metadata.get('shared_cache')
    _get_pair = getattr(_sc, 'get_source_and_ast', None)
    if callable(_get_pair):
        try:
            source, tree = _get_pair(fpath)
        except Exception:  # noqa: BLE001 — 鸭子类型缓存对象异常类型不可枚举
            _log.debug("[GuardQuality] SharedCache 源码/AST 对读取失败: %s",
                       fpath, exc_info=True)
        else:
            if isinstance(source, str) and '\ufffd' not in source:
                return source, tree if isinstance(tree, ast.Module) else None
            if isinstance(source, str):
                _log.warning(
                    "[GuardQuality] SharedCache 源码含 U+FFFD（解码降级），"
                    "回退直读: %s", fpath)
            elif source is not None:
                _log.warning(
                    "[GuardQuality] SharedCache 源码/AST 对返回形态违约"
                    "（期望 str|None，实际 %s），降级直读: %s",
                    type(source).__name__, fpath)
            return read_source_interpreter_encoding(fpath), None
    _cache, source = _cache_lookup(ctx, fpath)
    if source is not None:
        try:
            tree = _cache.get_ast(fpath)
        except Exception:  # noqa: BLE001 — 鸭子类型缓存对象异常类型不可枚举
            _log.debug("[GuardQuality] SharedCache get_ast 降级直读: %s",
                       fpath, exc_info=True)
        else:
            return source, tree if isinstance(tree, ast.Module) else None
    return read_source_interpreter_encoding(fpath), None
_GENERIC_SCAN_DIRS_NO_TEMP = GENERIC_SCAN_IGNORE_DIRS_LOWER - {'temp'}
def _is_scan_dir_segment(part: str) -> bool:
    if part.lower() == 'temp':
        return False
    return (is_audit_skip_dir(part) or is_backup_like_dir(part)
            or part.lower() in _GENERIC_SCAN_DIRS_NO_TEMP)
def _is_generic_scan_out_of_scope(fpath: str) -> bool:
    parts = [part for part in fpath.replace('\\', '/').split('/') if part]
    # ``.`` / ``..`` 是相对路径导航段而非目录名；若交给 is_audit_skip_dir
    # 会被 startswith('.') 当成隐藏目录，导致显式列出的 ``./x.py``、
    # ``sub/../x.py`` 被 G3/G7/G8/G14/G17 静默跳过。
    if any(_is_scan_dir_segment(part) for part in parts[:-1]
           if part not in ('.', '..')):
        return True
    if parts and parts[-1].startswith('.'):
        return True
    return is_test_file_path(fpath) or is_runtime_temp_path(fpath)
def _is_scan_candidate(fpath: Any) -> bool:
    return (isinstance(fpath, str) and is_py_source_file(fpath)
            and not _is_generic_scan_out_of_scope(fpath))
def _is_verifiable_py(fpath: Any) -> bool:
    return _is_scan_candidate(fpath) and os.path.isfile(fpath)
def _read_only_audit_target(ctx: OperationContext) -> str | None:
    if not is_read_only_audit(ctx):
        return None
    target = ctx.target_path
    if not isinstance(target, str):
        return None
    return target if target and (os.path.isdir(target)
                                 or os.path.isfile(target)) else None
def _dedupe_paths(paths: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    ordered: list[str] = []
    for path in paths:
        key = _result_identity(path)
        if key in seen:
            continue
        seen.add(key)
        ordered.append(path)
    return ordered
def resolve_guard_scan_targets(ctx: OperationContext) -> list[str]:
    affected = normalize_files_list(ctx.affected_files)
    audit_target = _read_only_audit_target(ctx)
    if audit_target is not None:
        if os.path.isfile(audit_target):
            extra = [audit_target] if _is_scan_candidate(audit_target) else []
            return _dedupe_paths([*affected, *extra])
        if not affected:
            return _dedupe_paths(_iter_directory_sources(audit_target))
        return _dedupe_paths(affected)
    target = target_path_str(ctx)
    if target and os.path.isfile(target) and _is_scan_candidate(target):
        return _dedupe_paths([*affected, target])
    return _dedupe_paths(affected)
def _pending_raw_code(ctx: OperationContext):
    metadata = getattr(ctx, 'metadata', None)
    if not hasattr(metadata, 'get') or 'code_to_write' not in metadata:
        return None
    return metadata.get('code_to_write')
def _pending_code(ctx: OperationContext) -> str | None:
    raw = _pending_raw_code(ctx)
    if isinstance(raw, str):
        return raw
    if isinstance(raw, (bytes, bytearray)):
        try:
            return bytes(raw).decode('utf-8')
        except UnicodeDecodeError:
            return None
    if isinstance(raw, (list, tuple)) and all(
            isinstance(line, str) for line in raw):
        return code_to_write_str(ctx)
    return None
def _pending_decode_error(ctx: OperationContext) -> str | None:
    raw = _pending_raw_code(ctx)
    if isinstance(raw, (list, tuple)) and not all(
            isinstance(line, str) for line in raw):
        return "待写入序列包含非 str 条目，无法完成文本校验"
    if raw is not None and not isinstance(
            raw, (str, bytes, bytearray, list, tuple)):
        return (f"待写入内容类型非法({type(raw).__name__})，"
                "无法完成文本校验")
    if not isinstance(raw, (bytes, bytearray)):
        return None
    try:
        bytes(raw).decode('utf-8')
    except UnicodeDecodeError as exc:
        return f"待写入 bytes 不是有效 UTF-8，无法完成文本校验: {exc}"
    return None
def _pending_byte_size(ctx: OperationContext, code: str | None) -> int | None:
    raw = _pending_raw_code(ctx)
    if isinstance(raw, (bytes, bytearray)):
        return len(raw)
    return _utf8_size(code) if code is not None else None
def _pending_code_is_python(target: str | None) -> bool:
    if not target:
        return True
    if is_py_source_file(target) or os.path.isdir(target):
        return True
    return not os.path.splitext(target)[1]
def _pending_write_target(ctx: OperationContext) -> str:
    target = ctx.target_path if isinstance(ctx.target_path, str) else ""
    affected = normalize_files_list(ctx.affected_files)
    if target and os.path.isdir(target) and len(affected) == 1:
        target_key = _result_identity(target)
        affected_key = _result_identity(affected[0])
        try:
            contained = os.path.commonpath(
                (target_key, affected_key)) == target_key
        except ValueError:
            contained = False
        if contained:
            return affected[0]
    return target
def _pending_write_source(ctx: OperationContext) -> tuple[str, str] | None:
    target = _pending_write_target(ctx)
    if not _pending_code_is_python(target):
        return None
    code = _pending_code(ctx)
    if code is None:
        return None
    return target or _VIRTUAL_PENDING_TARGET, code
def _iter_valid_targets(ctx: OperationContext) -> Iterator[str]:
    pending = _pending_write_source(ctx)
    pending_key = _result_identity(pending[0]) if pending else ""
    candidates = list(resolve_guard_scan_targets(ctx))
    if pending:
        candidates.append(pending[0])
    for fpath in _dedupe_paths(candidates):
        if pending_key and _result_identity(fpath) == pending_key:
            yield fpath
            continue
        if _is_verifiable_py(fpath):
            yield fpath
def iter_scan_sources(ctx: OperationContext) -> Iterator[tuple[str, str]]:
    pending = _pending_write_source(ctx)
    pending_key = _result_identity(pending[0]) if pending else ""
    for fpath in _iter_valid_targets(ctx):
        if pending and _result_identity(fpath) == pending_key:
            yield fpath, pending[1]
            continue
        try:
            yield fpath, _read_source_cached(ctx, fpath)
        except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
                MemoryError):
            _log.warning("[GuardQuality] 读取源码失败，跳过 %s",
                         fpath, exc_info=True)
            continue
def iter_scan_sources_with_ast(ctx: OperationContext) -> Iterator[tuple[str, str, ast.Module | None]]:
    pending = _pending_write_source(ctx)
    pending_key = _result_identity(pending[0]) if pending else ""
    for fpath in _iter_valid_targets(ctx):
        if pending and _result_identity(fpath) == pending_key:
            yield fpath, pending[1], parse_safe(pending[1])
            continue
        try:
            source, tree = _read_source_and_ast_cached(ctx, fpath)
        except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
                MemoryError):
            _log.warning("[GuardQuality] 读取源码失败，跳过 %s",
                         fpath, exc_info=True)
            continue
        yield fpath, source, tree
def _verify_file(fpath: str) -> tuple:
    try:
        source = read_source_interpreter_encoding(fpath)
        compile(source, fpath, "exec")
        return (True, "")
    except SyntaxError as e:
        _log.debug("[GuardQuality] 语法验证失败 %s: %s", fpath, e)
        return (False, (f"SyntaxError: {getattr(e, 'msg', '') or e}"
                        f" (line {getattr(e, 'lineno', 0) or 0})"))
    except LookupError as e:
        _log.debug("[GuardQuality] 源码编码无法确认 %s: %s", fpath, e)
        return (False, f"LookupError: {e}")
    except (OSError, UnicodeDecodeError, RecursionError, MemoryError,
            ValueError) as e:
        _log.warning("[GuardQuality] 语法验证无法读取 %s: %s", fpath, e)
        return (False, f"{type(e).__name__}: {e}")
def _cached_syntax_verdict(cache, fpath: str) -> tuple | None:
    _get_verdict = getattr(cache, "get_syntax_verdict", None)
    if not callable(_get_verdict):
        return None
    try:
        _cached = _get_verdict(fpath)
    except Exception as _e:  # noqa: BLE001 —— 鸭子类型缓存对象异常类型不可枚举
        log_swallowed(__name__, _e,
                      context=f'_cached_syntax_verdict:{type(_e).__name__}')
        return None
    if (isinstance(_cached, tuple) and len(_cached) == 2
            and isinstance(_cached[0], bool)
            and isinstance(_cached[1], str)):
        return _cached
    return None
def _source_tree_usable(src, tree) -> bool:
    return not (src is None or tree is None or not isinstance(src, str)
                or not isinstance(tree, ast.AST) or '\ufffd' in src)
def _verify_file_cached(fpath: str, cache) -> tuple:
    if cache is None:
        return _verify_file(fpath)
    _set_verdict = getattr(cache, "set_syntax_verdict", None)
    _cached = _cached_syntax_verdict(cache, fpath)
    if _cached is not None:
        return _cached
    try:
        src, tree = cache.get_source_and_ast(fpath)
    except Exception:  # noqa: BLE001 —— 鸭子类型缓存对象异常类型不可枚举，有意全量回退
        _log.warning("[GuardQuality] 共享缓存校验失败，回退直读 %s",
                     fpath, exc_info=True)
        verdict = _verify_file(fpath)
        _backfill_verdict(_set_verdict, fpath, verdict)
        return verdict
    if not _source_tree_usable(src, tree):
        verdict = _verify_file(fpath)
        _backfill_verdict(_set_verdict, fpath, verdict)
        return verdict
    try:
        compile(tree, fpath, "exec")
    except Exception:  # noqa: BLE001 —— compile(tree) 异常面随 CPython 版本演进不可枚举
        _log.warning("[GuardQuality] 缓存 AST 编译失败，回退直读 %s",
                     fpath, exc_info=True)
        verdict = _verify_file(fpath)
        _backfill_verdict(_set_verdict, fpath, verdict)
        return verdict
    verdict = (True, "")
    _backfill_verdict(_set_verdict, fpath, verdict)
    return verdict
def _backfill_verdict(set_verdict, fpath: str, verdict: tuple) -> None:
    if not callable(set_verdict):
        return
    try:
        set_verdict(fpath, ok=verdict[0], err=verdict[1])
    except Exception:  # noqa: BLE001 —— 回填是纯优化，失败不影响验证结论
        _log.debug("[GuardQuality] verdict 回填失败: %s", fpath, exc_info=True)
def _result_identity(p: str) -> str:
    return os.path.normcase(os.path.normpath(os.path.abspath(p)))
def _skip_scan_dir(dirname: str) -> bool:
    lowered = dirname.lower()
    return (is_audit_skip_dir(dirname)
            or is_backup_like_dir(dirname)
            or lowered in GENERIC_SCAN_IGNORE_DIRS_LOWER
            or lowered in TEST_ARTIFACT_DIRS)
def _walk_error(err: OSError) -> None:
    _log.warning("[GuardQuality] 目录遍历失败，跳过: %s: %s",
                 getattr(err, 'filename', ''), err)
def _iter_directory_sources(
        dirpath: str, *,
        is_candidate: Callable[[str], bool] = _is_scan_candidate,
) -> Iterator[str]:
    for root, dirs, files in os.walk(dirpath, onerror=_walk_error):
        dirs[:] = sorted(d for d in dirs if not _skip_scan_dir(d))
        for f in sorted(files):
            fpath = os.path.join(root, f)
            if not is_candidate(fpath):
                continue
            yield fpath
def _verify_paths(paths: Iterable[str], cache,
                  checked: set[str]) -> list[dict]:
    errors: list[dict] = []
    for fpath in paths:
        if not _is_verifiable_py(fpath):
            continue
        key = _result_identity(fpath)
        if key in checked:
            continue
        checked.add(key)
        ok, err = _verify_file_cached(fpath, cache)
        if not ok:
            errors.append({"file": fpath, "error": err})
    return errors
def _compile_source_error(fpath: str, source: str) -> dict | None:
    try:
        compile(source, fpath, "exec")
    except SyntaxError as exc:
        log_swallowed(__name__, exc, context='_compile_source_error:SyntaxError')
        return {"file": fpath,
                "error": (f"SyntaxError: 第 {getattr(exc, 'lineno', 0) or 0} 行: "
                          f"{getattr(exc, 'msg', '') or exc}")}
    except (ValueError, TypeError, MemoryError, RecursionError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_compile_source_error:{type(exc).__name__}')
        return {"file": fpath, "error": f"{type(exc).__name__}: {exc}"}
    return None
_CODE_WRITE_OPS = frozenset({
    OperationType.MODIFY_CODE, OperationType.REMOVE_CODE,
    OperationType.REFACTOR, OperationType.ADD_IMPORT,
    OperationType.CLEANUP, OperationType.SPLIT,
    OperationType.MERGE, OperationType.WRITE_FILE,
})
_SIZE_LIMIT_OPS = frozenset({
    OperationType.MODIFY_CODE, OperationType.WRITE_FILE,
    OperationType.REFACTOR, OperationType.ADD_IMPORT,
    OperationType.SPLIT, OperationType.MERGE,
})
def _syntax_scan_targets(ctx: OperationContext) -> list[str]:
    paths = list(resolve_guard_scan_targets(ctx))
    target = target_path_str(ctx)
    if target and os.path.isdir(target) and not paths:
        paths.extend(_iter_directory_sources(target))
    return _dedupe_paths(paths)
def _drop_shadowed_target(candidates: list[str], target: str | None) -> list[str]:
    if not target:
        return candidates
    target_key = _result_identity(target)
    return [p for p in candidates if _result_identity(p) != target_key]
def _syntax_failure_result(errors: list[dict]) -> GuardResult:
    details = [f"{e['file']}: {e['error']}" for e in errors[:10]]
    if len(errors) > 10:
        details.append(f"... 及其他 {len(errors) - 10} 个文件")
    return GuardResult(
        guard_name="G3", passed=False,
        level=GuardLevel.BLOCK,
        message=f"语法验证失败: {len(errors)} 个文件存在语法错误",
        details=details,
        fix_suggestion="修复所有语法错误后重试.可使用 compile() 逐文件验证."
    )
def guard_syntax(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G3", passed=True,
                           message="非代码修改操作,跳过语法检查")
    cache = ctx.metadata.get("shared_cache")
    candidates = _syntax_scan_targets(ctx)
    checked: set[str] = set()
    errors: list[dict] = []
    pending = _pending_write_source(ctx)
    if pending is not None:
        pending_target, code_to_write = pending
        code_err = _compile_source_error(pending_target, code_to_write)
        if code_err is not None:
            errors.append(code_err)
        candidates = _drop_shadowed_target(candidates, pending_target)
    else:
        decode_error = _pending_decode_error(ctx)
        pending_target = _pending_write_target(ctx)
        if decode_error is not None and _pending_code_is_python(pending_target):
            label = pending_target or _VIRTUAL_PENDING_TARGET
            errors.append({"file": label, "error": decode_error})
            candidates = _drop_shadowed_target(candidates, pending_target)
    errors.extend(_verify_paths(candidates, cache, checked))
    if errors:
        return _syntax_failure_result(errors)
    return GuardResult(guard_name="G3", passed=True,
                       message="所有文件语法验证通过")
_TRIPLE_DQ = '"""'
_TRIPLE_SQ = "'''"
_PASS_THEN_TRIPLE_RE = re.compile(
    r"pass(?=$|[\s;])\s*;?\s*[fFrRbBuU]{0,2}(?:'''|\"\"\")")
def _strip_line_comment(line: str) -> str:
    quote = None
    index = 0
    length = len(line)
    while index < length:
        ch = line[index]
        if quote is not None:
            if ch == "\\":
                index += 2
                continue
            if ch == quote:
                quote = None
        elif ch in ("'", '"'):
            quote = ch
        elif ch == "#":
            return line[:index]
        index += 1
    return line
def _tokenize_source(source: str):
    token_source = "\n".join(ast_split_lines(source))
    try:
        return list(tokenize.generate_tokens(
            io.StringIO(token_source).readline))
    except (tokenize.TokenError, IndentationError, SyntaxError,
            ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_tokenize_source:{type(_e).__name__}')
        return None
def _unclosed_triple_quote_issue(source: str) -> tuple[int, str] | None:
    text = "\n".join(ast_split_lines(source))
    counts = {_TRIPLE_DQ: 0, _TRIPLE_SQ: 0}
    quote: str | None = None
    open_triple: str | None = None
    open_offset = 0
    index = 0
    length = len(text)
    while index < length:
        ch = text[index]
        if quote is not None:
            if ch == "\\":
                index += 2
                continue
            if len(quote) == 3 and text.startswith(quote, index):
                counts[quote] += 1
                quote = None
                open_triple = None
                index += 3
                continue
            if ch == quote:
                quote = None
                index += 1
                continue
            if ch == "\n" and len(quote) == 1:
                quote = None
            index += 1
            continue
        if ch == "#":
            newline = text.find("\n", index)
            if newline < 0:
                break
            index = newline
            continue
        if ch in ("'", '\"'):
            delimiter = (ch * 3 if text.startswith(ch * 3, index) else ch)
            quote = delimiter
            if len(delimiter) == 3:
                open_triple = delimiter
                open_offset = index
                counts[delimiter] += 1
            index += len(delimiter)
            continue
        index += 1
    if open_triple is None:
        return None
    label = "三双引号" if open_triple == _TRIPLE_DQ else "三单引号"
    count = counts[open_triple]
    line_no = text.count("\n", 0, open_offset) + 1
    return (line_no, f"{label} {open_triple} 不成对（共 {count} 个）")
def find_unclosed_triple_quotes(source: str) -> list[tuple[int, str]]:
    if not isinstance(source, str):
        return []
    try:
        parse_cached(source)
        return []
    except (SyntaxError, ValueError, RecursionError, MemoryError) as e:
        _log.debug("降级容错路径触发（静默留痕）: %s", e)
    if _tokenize_source(source) is not None:
        return []
    issue = _unclosed_triple_quote_issue(source)
    return [issue] if issue is not None else []
_DOCSTRING_SYNTAX_MARKERS = (
    "triple-quoted string", "invalid character", "U+FF",
)
def _is_unclosed_triple_error(err: SyntaxError) -> bool:
    return "triple-quoted string" in f"{getattr(err, 'msg', '') or ''} {err}"
def _is_docstring_syntax_error(err: SyntaxError) -> bool:
    text = f"{getattr(err, 'msg', '') or ''} {err}"
    return any(marker in text for marker in _DOCSTRING_SYNTAX_MARKERS)
def _docstring_syntax_desc(err: SyntaxError) -> str:
    if 'invalid character' in str(err) or 'U+FF' in str(err):
        return (f"可能存在 docstring 边界破坏,"
                f"导致中文标点泄漏到代码层: {err.msg}")
    return f"语法错误可能由 docstring 边界破坏引起: {err.msg}"
def _check_docstring_integrity(
        source: str, *, has_unclosed_triple: bool = False,
) -> list[tuple[int, str]]:
    issues: list[tuple[int, str]] = []
    if not isinstance(source, str):
        return issues
    try:
        parse_cached(source)
    except SyntaxError as e:
        if has_unclosed_triple and _is_unclosed_triple_error(e):
            _log.debug("[GuardQuality] 未闭合三引号已由词法探针报告: %s", e)
        elif _is_docstring_syntax_error(e):
            _log.warning("[GuardQuality] docstring 边界导致语法错误: %s", e)
            issues.append((e.lineno or 0, _docstring_syntax_desc(e)))
        else:
            _log.debug("[GuardQuality] 普通语法错误（交由 G3）: %s", e)
    except ValueError as e:
        _log.warning("[GuardQuality] ast.parse ValueError", exc_info=True)
        issues.append((
            0,
            f"源码不可解析（可能含 null bytes）: {e}"
        ))
    except (RecursionError, MemoryError) as e:
        _log.warning("[GuardQuality] ast.parse %s", type(e).__name__,
                     exc_info=True)
        issues.append((
            0,
            f"源码不可解析（嵌套过深）: {e}"
        ))
    return issues
_ORPHAN_TRIPLE_LINE_RE = re.compile(r"[fFrRbBuU]*('''|\"\"\")")
_TRIPLE_START_TOKEN_TYPES: frozenset[int] = frozenset(
    _tok_type for _tok_type in (tokenize.STRING,
                                getattr(tokenize, 'FSTRING_START', None))
    if _tok_type is not None
)
_ORPHAN_PREV_EXEMPT_PREFIXES = ('def ', 'class ', '@', 'async def',
                                'import ', 'from ')
def _prev_code_line(lines: list[str], idx: int) -> str:
    pl = idx
    while pl >= 0:
        s = _strip_line_comment(lines[pl]).strip()
        if s:
            return s
        pl -= 1
    return ""
def _orphan_prev_exempt(prev: str) -> bool:
    return (prev.startswith(_ORPHAN_PREV_EXEMPT_PREFIXES)
            or prev.endswith((_TRIPLE_DQ, _TRIPLE_SQ, ':')))
def _pass_replaced_docstring_issues(lines: list[str], toks) -> list[tuple[int, str]]:
    issues: list[tuple[int, str]] = []
    if toks is None:
        return issues
    pass_lines = {
        tok.start[0] for tok in toks
        if tok.type == tokenize.NAME and tok.string == 'pass'
    }
    for i in sorted(pass_lines):
        if i > len(lines) or not _PASS_THEN_TRIPLE_RE.match(lines[i - 1].strip()):
            continue
        stripped = lines[i - 1].strip()
        issues.append((
            i,
            f"第 {i} 行 pass 语句后紧跟三引号,可能是 docstring 开头被 pass 替换: `{stripped[:60]}`"
        ))
    return issues
def _orphan_line_issue(lines: list[str], lineno: int, m, dq_state: int,
                       sq_state: int) -> tuple[int, str] | None:
    in_str = ((dq_state % 2 == 1) if m.group(1) == _TRIPLE_DQ
              else (sq_state % 2 == 1))
    if in_str:
        return None
    prev = _prev_code_line(lines, lineno - 2)
    if not prev or _orphan_prev_exempt(prev):
        return None
    return (lineno,
            (f"第 {lineno} 行发现孤立的 docstring 三引号,"
             f"上一行是普通代码: `{prev[:60]}`"))
def _orphan_start_issues_by_state(lines: list[str]) -> list[tuple[int, str]]:
    issues: list[tuple[int, str]] = []
    dq_state = 0
    sq_state = 0
    for i, line in enumerate(lines, 1):
        code = _strip_line_comment(line).strip()
        if not code:
            continue
        m = _ORPHAN_TRIPLE_LINE_RE.fullmatch(code)
        issue = (_orphan_line_issue(lines, i, m, dq_state, sq_state)
                 if m and i > 1 else None)
        if issue is not None:
            issues.append(issue)
        dq_state += code.count(_TRIPLE_DQ)
        sq_state += code.count(_TRIPLE_SQ)
    return issues
def _find_broken_docstring_start(source: str) -> list[tuple[int, str]]:
    if not isinstance(source, str):
        return []
    lines = ast_split_lines(source)
    toks = _tokenize_source(source)
    issues = _pass_replaced_docstring_issues(lines, toks)
    token_issues = _isolated_triple_quote_tokens(source, toks)
    if token_issues is not None:
        issues.extend(token_issues)
        return issues
    issues.extend(_orphan_start_issues_by_state(lines))
    return issues
def _paren_depth_after(depth: int, tok) -> int:
    if tok.type != tokenize.OP:
        return depth
    if tok.string in "([{":
        return depth + 1
    if tok.string in ")]}":
        return max(0, depth - 1)
    return depth
def _orphan_token_issue(tok, lines: list[str],
                        paren_depth: int) -> tuple[int, str] | None:
    if paren_depth > 0 or tok.type not in _TRIPLE_START_TOKEN_TYPES:
        return None
    m = _ORPHAN_TRIPLE_LINE_RE.match(tok.string)
    if not m:
        return None
    start_line = tok.start[0]
    if start_line - 1 >= len(lines):
        return None
    line_txt = lines[start_line - 1].strip()
    if not _ORPHAN_TRIPLE_LINE_RE.fullmatch(line_txt):
        return None
    prev = _prev_code_line(lines, start_line - 2)
    if prev and not _orphan_prev_exempt(prev):
        return (start_line,
                (f"第 {start_line} 行发现孤立的 docstring 三引号,"
                 f"上一行是普通代码: `{prev[:60]}`"))
    return None
def _isolated_triple_quote_tokens(source: str, toks) -> list[tuple[int, str]] | None:
    if toks is None:
        return None
    lines = ast_split_lines(source)
    out: list[tuple[int, str]] = []
    _paren_depth = 0
    for tok in toks:
        _paren_depth = _paren_depth_after(_paren_depth, tok)
        issue = _orphan_token_issue(tok, lines, _paren_depth)
        if issue is not None:
            out.append(issue)
    return out
def _docstring_issues_for_source(fpath: str, source: str) -> list[str]:
    name = os.path.basename(fpath)
    lexical = find_unclosed_triple_quotes(source)
    issues = [f"{name}:{line_no}: {desc}" for line_no, desc in lexical]
    for line_no, desc in _check_docstring_integrity(
            source, has_unclosed_triple=bool(lexical)):
        issues.append(f"{name}:{line_no}: {desc}")
    for line_no, desc in _find_broken_docstring_start(source):
        issues.append(f"{name}:{line_no}: {desc}")
    return issues
def guard_docstring(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G8", passed=True,
                           message="非代码修改操作,跳过 docstring 检查")
    issues: list[str] = []
    for fpath, source in iter_scan_sources(ctx):
        issues.extend(_docstring_issues_for_source(fpath, source))
    if issues:
        details = issues[:10]
        if len(issues) > 10:
            details.append(f"... 及其他 {len(issues) - 10} 个问题")
        return GuardResult(
            guard_name="G8", passed=False,
            level=GuardLevel.BLOCK,
            message=f"docstring 边界检查发现 {len(issues)} 个问题",
            details=details,
            fix_suggestion="修复 docstring 边界.确保三引号成对出现,"
                           "docstring 内容未被泄漏到代码层."
        )
    return GuardResult(guard_name="G8", passed=True,
                       message="docstring 边界检查通过")
def _file_issues(fpath: str, messages: list[str]) -> list[str]:
    name = os.path.basename(fpath)
    return [f"{name}: {message}" for message in messages]
def _as_name_list(value) -> list[str]:
    if isinstance(value, (list, tuple, set)):
        return [x for x in value if isinstance(x, str)]
    return []
def _non_str_code_notes(before_code, after_code) -> list[str]:
    return [
        f"{_name}(实际 {type(_code).__name__},期望 str)"
        for _name, _code in (("before_code", before_code),
                             ("after_code", after_code))
        if not isinstance(_code, str)
    ]
_METADATA_TYPE_FIX = ("检查 metadata 中 before_code/after_code 的填充逻辑,"
                      "两者须为完整源码字符串.")
def _before_after_type_gate(ctx: OperationContext, action: str
                            ) -> tuple[list[str], str | None, str | None]:
    if ("before_code" not in ctx.metadata
            and "after_code" not in ctx.metadata):
        return [], None, None
    before_code = ctx.metadata.get("before_code", "")
    after_code = ctx.metadata.get("after_code", "")
    bad = _non_str_code_notes(before_code, after_code)
    if bad:
        return [f"{' 与 '.join(bad)} 类型无效,{action}无法执行"], None, None
    missing = [
        name for name in ("before_code", "after_code")
        if name not in ctx.metadata
    ]
    if missing:
        return [
            (f"{' 与 '.join(missing)} 缺失,before_code/after_code 须成对提供,"
             f"{action}无法执行")
        ], None, None
    if not before_code and not after_code:
        return [], None, None
    return [], before_code, after_code
@dataclass(frozen=True)
class _GuardVerdictSpec:
    guard_name: str
    pass_message: str
    found_prefix: str
    content_fix: str
    block_level: bool = True
def _code_guard_verdict(spec: _GuardVerdictSpec, issues: list[str],
                        type_notes: list[str]) -> GuardResult:
    if issues or type_notes:
        return GuardResult(
            guard_name=spec.guard_name, passed=False,
            level=(GuardLevel.BLOCK if (spec.block_level and issues)
                   else GuardLevel.WARN),
            message=(f"{spec.found_prefix}发现 "
                     f"{len(issues) + len(type_notes)} 个问题"),
            details=(issues + type_notes)[:10],
            fix_suggestion=(spec.content_fix if issues else _METADATA_TYPE_FIX))
    return GuardResult(guard_name=spec.guard_name, passed=True,
                       message=spec.pass_message)
_FSTRING_START_TOKEN = getattr(tokenize, "FSTRING_START", -1)
_FSTRING_END_TOKEN = getattr(tokenize, "FSTRING_END", -1)
def _scan_field_end(segment: str, start: int) -> tuple[int, int]:
    depth = 1
    j = start
    n = len(segment)
    while j < n and depth > 0:
        if segment[j] == "{":
            depth += 1
        elif segment[j] == "}":
            depth -= 1
        j += 1
    return j, depth
def _format_spec_start(field: str) -> int | None:
    closers = {')': '(', ']': '[', '}': '{'}
    stack: list[str] = []
    quote: str | None = None
    index = 0
    while index < len(field):
        ch = field[index]
        if quote is not None:
            if ch == "\\":
                index += 2
                continue
            if field.startswith(quote, index):
                index += len(quote)
                quote = None
                continue
            index += 1
            continue
        if ch in ("'", '"'):
            quote = ch * 3 if field.startswith(ch * 3, index) else ch
            index += len(quote)
            continue
        if ch in "([{":
            stack.append(ch)
        elif ch in ")]}":
            if stack and stack[-1] == closers[ch]:
                stack.pop()
        elif ch == ":" and not stack:
            return index + 1
        index += 1
    return None
def _iter_format_fields_with_pos(segment: str):
    i = 0
    n = len(segment)
    while i < n:
        c = segment[i]
        if c == "{":
            if i + 1 < n and segment[i + 1] == "{":
                i += 2
                continue
            j, depth = _scan_field_end(segment, i + 1)
            if depth == 0:
                field_start = i + 1
                field = segment[field_start:j - 1]
                yield i, field
                spec_start = _format_spec_start(field)
                if spec_start is not None:
                    for nested_off, nested_field in _iter_format_fields_with_pos(
                            field[spec_start:]):
                        yield (field_start + spec_start + nested_off,
                               nested_field)
            i = j
        elif c == "}":
            i += 2 if (i + 1 < n and segment[i + 1] == "}") else 1
        else:
            i += 1
def _iter_fstring_segments(source: str, line_starts: list[int]):
    def _offset(position) -> int:
        return line_starts[position[0] - 1] + position[1]
    start_offsets: list[int] = []
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            if tok.type == tokenize.STRING:
                prefix = re.match(
                    r"([A-Za-z]*)(?:'''|\"\"\"|'|\")", tok.string)
                if prefix and "f" in prefix.group(1).lower():
                    yield _offset(tok.start), tok.string
            elif tok.type == _FSTRING_START_TOKEN:
                start_offsets.append(_offset(tok.start))
            elif tok.type == _FSTRING_END_TOKEN and start_offsets:
                start = start_offsets.pop()
                yield start, source[start:_offset(tok.end)]
    except (tokenize.TokenError, IndentationError, SyntaxError,
            ValueError) as exc:
        log_swallowed(__name__, exc,
                      context=f'_iter_fstring_segments:{type(exc).__name__}')
def _find_empty_braces(source: str) -> list[tuple[int, str]]:
    text = "\n".join(ast_split_lines(source))
    empty_braces = []
    line_starts = [0]
    line_starts.extend(m.end() for m in re.finditer(r"\n", text))
    for seg_base, segment in _iter_fstring_segments(text, line_starts):
        for brace_off, field in _iter_format_fields_with_pos(segment):
            expression = field.strip()
            if expression and not expression.startswith((":", "!", "=")):
                continue
            line_no = bisect.bisect_right(
                line_starts, seg_base + brace_off)
            line_start = line_starts[line_no - 1]
            line_end = text.find("\n", line_start)
            line = (text[line_start:] if line_end == -1
                    else text[line_start:line_end])
            empty_braces.append((line_no, line.strip()))
    return empty_braces
def _count_expression_name_loads(node: ast.AST) -> int:
    if isinstance(node, ast.JoinedStr):
        return 0
    own = int(isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load))
    return own + sum(
        _count_expression_name_loads(child)
        for child in ast.iter_child_nodes(node)
    )
def _count_fstring_vars(source: str) -> int | None:
    tree = parse_safe(source)
    if tree is None:
        return None
    count = 0
    for node in walk_nodes(tree):
        if isinstance(node, ast.JoinedStr):
            for value in node.values:
                if isinstance(value, ast.FormattedValue):
                    count += _count_expression_name_loads(value.value)
    return count
def _scan_empty_brace_issues(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    for fpath, source in iter_scan_sources(ctx):
        if parse_safe(source) is not None:
            continue
        issues.extend(_file_issues(fpath, [
            f"{line_no}: f-string 中存在空花括号: `{line_content[:80]}`"
            for line_no, line_content in _find_empty_braces(source)
        ]))
    return issues
def guard_fstring(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G7", passed=True,
                           message="非代码修改操作,跳过 f-string 检查")
    issues = _scan_empty_brace_issues(ctx)
    type_notes, _before, _after = _before_after_type_gate(ctx, "变量引用计数对比")
    if _before is not None:
        before_count = _count_fstring_vars(_before)
        after_count = _count_fstring_vars(_after)
        if (before_count is not None and after_count is not None
                and after_count < before_count):
            diff = before_count - after_count
            issues.append(
                f"f-string 变量引用减少 {diff} 个（{before_count} → {after_count}）,"
                f"可能存在变量名被误删"
            )
    return _code_guard_verdict(
        _GuardVerdictSpec(
            "G7", "f-string 变量检查通过", "f-string 检查",
            "修复 f-string 中的空花括号,确保变量名未被误删."),
        issues, type_notes)
def _read_source_optional(ctx: OperationContext, fpath: str) -> str | None:
    try:
        return _read_source_cached(ctx, fpath)
    except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
            MemoryError) as e:
        _log.warning("[GuardQuality] 跳过不可读文件 %s: %s", fpath, e)
        return None
EXECUTABLE_EXTENSIONS = {'.py', '.sh', '.bash', '.js', '.ts', '.bat', '.cmd', '.ps1'}
def _is_executable(filepath: str) -> bool:
    ext = os.path.splitext(filepath)[1].lower()
    return ext in EXECUTABLE_EXTENSIONS
def _content_diag_targets(ctx: OperationContext) -> list[str]:
    affected = normalize_files_list(ctx.affected_files)
    target = target_path_str(ctx)
    candidates = [*affected, *([target] if target else [])]
    if target and os.path.isdir(target) and not affected:
        candidates.extend(_iter_directory_sources(
            target, is_candidate=_is_content_source_candidate))
    return _dedupe_paths(candidates)
def _is_content_scan_candidate(fpath: Any) -> bool:
    return (isinstance(fpath, str) and bool(fpath)
            and os.path.isfile(fpath)
            and not _is_generic_scan_out_of_scope(fpath))
def _is_content_source_candidate(fpath: Any) -> bool:
    return (isinstance(fpath, str) and _is_executable(fpath)
            and _is_content_scan_candidate(fpath))
def _scan_affected_files_dangerous(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    pending_code = _pending_code(ctx)
    if (pending_code is None
            and ctx.operation in (OperationType.REMOVE_CODE,
                                  OperationType.CLEANUP)):
        return issues
    target = _pending_write_target(ctx)
    pending_key = (_result_identity(target)
                   if _pending_raw_code(ctx) is not None and target else '')
    for fpath in _content_diag_targets(ctx):
        if not _is_content_source_candidate(fpath):
            continue
        if pending_key and _result_identity(fpath) == pending_key:
            continue
        content = _read_source_optional(ctx, fpath)
        if content is None:
            continue
        issues.extend(scan_content_dangerous(content, fpath))
    return issues
def guard_content_diag(ctx: OperationContext) -> GuardResult:
    if ctx.operation not in _CODE_WRITE_OPS:
        return GuardResult(guard_name="G14", passed=True,
                           message="非代码修改操作,跳过内容诊断")
    if ctx.metadata.get("content_diag_bypass") is True:
        return GuardResult(guard_name="G14", passed=True,
                           message="人工豁免(content_diag_bypass),跳过内容诊断")
    issues: list[str] = []
    issues.extend(_scan_affected_files_dangerous(ctx))
    code_to_write = _pending_code(ctx)
    if code_to_write is not None:
        issues.extend(scan_content_dangerous(
            code_to_write, content_label(ctx)))
    else:
        decode_error = _pending_decode_error(ctx)
        if decode_error is not None:
            issues.append(f"{content_label(ctx)}: {decode_error}")
    return issues_guard_result(
        "G14", "内容诊断", "危险模式", issues,
        "审查以上危险模式.如果是合法操作,请在 metadata 中设置 "
        "content_diag_bypass=True.",
        "内容诊断通过",
        level=GuardLevel.WARN)
DEFAULT_MAX_FILE_SIZE = 10 * 1024 * 1024
DEFAULT_MAX_TOTAL_SIZE = 50 * 1024 * 1024
DEFAULT_MAX_LINES = 5000
DEFAULT_MAX_FILE_COUNT = 100
def _get_file_size(filepath: str) -> int | None:
    try:
        return os.path.getsize(filepath)
    except (OSError, ValueError):
        _log.warning("[GuardQuality] 文件大小无法读取 %s",
                     filepath, exc_info=True)
        return None
def _utf8_size(text: str) -> int:
    return len(text.encode('utf-8', errors='replace'))
def _g17_code_issues(code_to_write: str,
                     pending_size: int | None = None) -> list[str]:
    issues: list[str] = []
    if not code_to_write and not pending_size:
        return issues
    size = (_utf8_size(code_to_write)
            if pending_size is None else pending_size)
    if size > DEFAULT_MAX_FILE_SIZE:
        issues.append(
            f"待写入内容 {size / 1024 / 1024:.1f}MB 超过单文件上限 "
            f"{DEFAULT_MAX_FILE_SIZE / 1024 / 1024:.0f}MB."
        )
    lines = count_lines(code_to_write) if code_to_write else 0
    if lines > DEFAULT_MAX_LINES:
        issues.append(
            f"待写入内容 {lines} 行超过单文件上限 {DEFAULT_MAX_LINES} 行."
            "建议按 GOV-01 简化/去重/迁移无关块，禁止拆分文件规避."
        )
    return issues
def _g17_size_paths(affected: list[str],
                    pending_target: str) -> list[str]:
    return _dedupe_paths(
        [*affected, *([pending_target] if pending_target else [])])
def _g17_existing_file_line_issue(fpath: str) -> str | None:
    if not is_py_source_file(fpath):
        return None
    try:
        source = read_source_interpreter_encoding(fpath)
    except (OSError, UnicodeDecodeError, SyntaxError, LookupError,
            MemoryError, ValueError) as exc:
        log_swallowed(
            __name__, exc,
            context=f'_g17_existing_file_line_issue:{type(exc).__name__}')
        return (f"文件 {os.path.basename(fpath)} 行数无法确认,"
                "不能按未超限放行.请检查文件编码与读取状态.")
    lines = count_lines(source)
    if lines <= DEFAULT_MAX_LINES:
        return None
    return (f"文件 {os.path.basename(fpath)} 已 {lines} 行,"
            f"超过单文件上限 {DEFAULT_MAX_LINES} 行."
            "请先按 GOV-01 简化/去重/迁移无关块后再操作"
            "（禁止拆分文件规避）.")
def _g17_measure_size_paths(
        size_paths: list[str], pending_target: str, pending_code: str | None,
        pending_size: int | None = None) -> tuple[int, list[str]]:
    issues: list[str] = []
    pending_active = pending_code is not None or pending_size is not None
    pending_key = (_result_identity(pending_target)
                   if pending_active and pending_target else '')
    if pending_size is None:
        pending_size = (_utf8_size(pending_code)
                        if pending_code is not None else 0)
    pending_counted = False
    total_size = 0
    for fpath in size_paths:
        if pending_key and _result_identity(fpath) == pending_key:
            total_size += pending_size
            pending_counted = True
            continue
        if not os.path.isfile(fpath):
            continue
        size = _get_file_size(fpath)
        if size is None:
            issues.append(
                f"文件 {os.path.basename(fpath)} 大小无法确认,"
                "不能按零字节放行.请检查路径权限与文件状态."
            )
            continue
        total_size += size
        line_issue = _g17_existing_file_line_issue(fpath)
        if line_issue is not None:
            issues.append(line_issue)
        if size > DEFAULT_MAX_FILE_SIZE:
            issues.append(
                f"文件 {os.path.basename(fpath)} 已 "
                f"{size / 1024 / 1024:.1f}MB,超过单文件上限."
                "请先按 GOV-01 简化/去重/迁移无关块后再操作"
                "（禁止拆分文件规避）."
            )
    if pending_active and not pending_counted:
        total_size += pending_size
    return total_size, issues
def _g17_is_runtime_artifact(fpath: str) -> bool:
    """运行时产物（日志/报告/备份）不计入源码体积门禁。

    ``DEFAULT_MAX_FILE_SIZE`` / ``DEFAULT_MAX_LINES`` 是**源码**体积上限，
    目的是阻止把源文件写成巨型模块。日志（``log/*.log``，自身有 20MB 轮转
    闸）与 HTML/JSON 报告属于运行时产出，体积与源码复杂度无关，计入后会
    让整个技能因为一份 17.8MB 日志而永久交付阻断（G17 属 P0）。
    """
    if not isinstance(fpath, str) or not fpath:
        return False
    parts = [part for part in fpath.replace('\\', '/').split('/') if part]
    if not parts:
        return False
    if parts[-1].lower().endswith(('.log', '.jsonl', '.html', '.htm')):
        return True
    return any(part.lower() in _G17_RUNTIME_DIRNAMES for part in parts[:-1])
_G17_RUNTIME_DIRNAMES: frozenset[str] = frozenset({
    'log', 'htm', 'zhenduan', 'temp', 'jinhua', '_backups', '__pycache__',
})
def _g17_affected_issues(
        affected: list[str], pending_target: str, pending_code: str | None,
        pending_size: int | None = None,
        directory_audit: bool = False) -> list[str]:
    size_paths = [
        path for path in _g17_size_paths(affected, pending_target)
        if not os.path.isdir(path) and not _g17_is_runtime_artifact(path)]
    issues: list[str] = []
    # 文件数上限是**单次写入扇出**护栏（一次操作波及多少文件），不是目录
    # 规模上限。目录审计天然覆盖全量源文件（本仓 307 个模块 > 100），此时
    # 计数没有护栏意义，只会把只读审计永久卡死。
    if not directory_audit and len(size_paths) > DEFAULT_MAX_FILE_COUNT:
        issues.append(
            f"受影响文件 {len(size_paths)} 个超过上限 "
            f"{DEFAULT_MAX_FILE_COUNT} 个."
        )
    total_size, size_issues = _g17_measure_size_paths(
        size_paths, pending_target, pending_code, pending_size)
    issues.extend(size_issues)
    if total_size > DEFAULT_MAX_TOTAL_SIZE:
        issues.append(
            f"受影响文件总大小 {total_size / 1024 / 1024:.1f}MB 超过上限 "
            f"{DEFAULT_MAX_TOTAL_SIZE / 1024 / 1024:.0f}MB."
        )
    return issues
def guard_size_limit(ctx: OperationContext) -> GuardResult:
    pending_code = _pending_code(ctx)
    pending_raw = _pending_raw_code(ctx)
    pending_size = _pending_byte_size(ctx, pending_code)
    if ctx.operation not in _SIZE_LIMIT_OPS and pending_raw is None:
        return GuardResult(guard_name="G17", passed=True,
                           message="非写入操作,跳过大小检查")
    issues = _g17_code_issues(pending_code or '', pending_size)
    if ctx.operation in _SIZE_LIMIT_OPS:
        affected = list(normalize_files_list(ctx.affected_files))
        target = (_pending_write_target(ctx) if pending_raw is not None
                  else target_path_str(ctx))
        directory_audit = bool(
            is_read_only_audit(ctx) and not affected and target
            and os.path.isdir(target))
        if directory_audit:
            affected = list(_iter_directory_sources(
                target, is_candidate=_is_content_source_candidate))
        issues += _g17_affected_issues(
            affected, target, pending_code, pending_size,
            directory_audit=directory_audit)
    return issues_guard_result(
        "G17", "文件大小检查", "超限", issues,
        "按 GOV-01 简化/去重/迁移无关块、减少单次操作文件数量"
        "（文件上限不得以拆分规避）."
        f" 当前限制: {DEFAULT_MAX_FILE_SIZE / 1024 / 1024:.0f}MB/文件, "
        f"{DEFAULT_MAX_LINES}行/文件, {DEFAULT_MAX_FILE_COUNT}文件/任务.",
        "文件大小检查通过")
DANGEROUS_SYSCALLS = [
    (r'\bos\.system\s*\(', 'os.system() 调用'),
    (r'\bos\.popen\s*\(', 'os.popen() 调用'),
    (r'\bsubprocess\.(call|run|Popen|check_call|check_output)\s*\(',
     'subprocess 调用'),
    (r'(?:(?<!\.)\beval|\bbuiltins\.eval)\s*\(', 'eval() 调用'),
    (r'(?:(?<!\.)\bexec|\bbuiltins\.exec)\s*\(', 'exec() 调用'),
    (r'\b__import__\s*\(', '__import__() 动态导入'),
    (r'(?:(?<!\.)\bcompile|\bbuiltins\.compile)\s*\(',
     'compile() 动态编译'),
    (r'\bexecfile\s*\(', 'execfile() 调用'),
]
DANGEROUS_FILE_OPS = [
    (r'\brm\s+-(?:r|rf|fr)\b', 'rm -rf 递归删除'),
    (r'\bos\.remove\s*\(', 'os.remove() 删除文件'),
    (r'\bos\.rmdir\s*\(', 'os.rmdir() 删除目录'),
    (r'\bshutil\.rmtree\s*\(', 'shutil.rmtree() 递归删除'),
    (r'\bos\.unlink\s*\(', 'os.unlink() 删除文件'),
    (r'\bchmod\s+777\b', 'chmod 777 危险权限'),
    (r'\bchmod\s+-R\b', 'chmod -R 递归改权限'),
    (r'\bos\.f?chmod\b[^\n]*\b0(?:o777|o775|x1ff|x1fd)\b',
     'os.chmod() 危险权限 (0o777/0o775)'),
]
DANGEROUS_NETWORK = [
    (r'curl\s+.*\|\s*(ba)?sh', 'curl | sh 管道执行'),
    (r'wget\s+.*-O\s*-.*\|\s*(ba)?sh', 'wget | sh 管道执行'),
    (r'curl\s+.*\|\s*python', 'curl | python 管道执行'),
]
DANGEROUS_PRIVILEGE = [
    (r'\bsudo\b', 'sudo 权限提升'),
    (r'(?:^\s*|\$\(\s*|[;&|]\s*|\b(?:then|do|else)\s+|\bsudo\s+)su\s+-', 'su 切换用户'),
    (r'\bchown\b', 'chown 更改所有者'),
    (r'\bchattr\b', 'chattr 更改文件属性'),
]
_INFO_LEAK_VALUE = (
    r"\(?[fFrRbBuU]{0,2}"
    r"(?:\"{3}(?:(?:\\.|[^\"\\\n])){4,}\"{3}"
    r"|'''(?:(?:\\.|[^'\\\n])){4,}'''"
    r"|\"(?:(?:\\.|[^\"\\\n])){4,}\""
    r"|'(?:(?:\\.|[^'\\\n])){4,}')"
)
_INFO_LEAK_KEY_CLOSER = r"[\"']?\]?"
_INFO_LEAK_TAIL = (
    r"(?:" + _INFO_LEAK_KEY_CLOSER + r"\s*(?<![=!<>])=(?!=)\s*"
    + _INFO_LEAK_VALUE
    + r"|[\"']?\s*:\s*" + _INFO_LEAK_VALUE + r")"
)
DANGEROUS_INFO_LEAK = [
    (rf'(?:\b|_)password\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码密码'),
    (rf'(?:\b|_)passwd\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码密码'),
    (rf'(?:\b|_)secret(?:[_-]?key)?\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码密钥'),
    (rf'(?:\b|_)api[_-]?key\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码 API Key'),
    (rf'(?:\b|_)token\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码 Token'),
    (rf'(?:\b|_)access[_-]?key\s*(:\s*[\w\[\]., |]+\s*)?{_INFO_LEAK_TAIL}', '硬编码访问密钥'),
]
ALL_DANGEROUS_PATTERNS = (
    DANGEROUS_SYSCALLS + DANGEROUS_FILE_OPS +
    DANGEROUS_NETWORK + DANGEROUS_PRIVILEGE +
    DANGEROUS_INFO_LEAK
)
_COMPILED_DANGEROUS_PATTERNS = tuple(
    (re.compile(pattern, re.IGNORECASE), description)
    for pattern, description in ALL_DANGEROUS_PATTERNS)
_DEFINITION_EXEMPT_DESCRIPTIONS = frozenset({
    'eval() 调用', 'exec() 调用', 'compile() 动态编译',
})
_DEFAULT_CONTENT_LABEL = "<code>"
def _is_definition_site(line: str, start: int) -> bool:
    return bool(re.search(r'\bdef$', line[:start].rstrip()))
def _masked_content_spans(content: str) -> list[tuple[int, int]]:
    """返回注释、docstring、路径守卫与规则表字面量的字符跨度。"""
    try:
        from jwsgj.skill_scan_kernels import _text_evidence_mask
        mask = _text_evidence_mask(content)
    except (ImportError, AttributeError, ValueError, TypeError):
        return []
    return mask or []
def scan_content_dangerous(
        content: str, filepath: str = _DEFAULT_CONTENT_LABEL) -> list[str]:
    if not isinstance(content, str):
        return []
    findings: list[str] = []
    lines = ast_split_lines(content)
    masked_spans = _masked_content_spans(content)
    line_starts = [0]
    line_starts.extend(
        match.end() for match in re.finditer(r"\r\n|\r|\n", content))
    for pattern, description in _COMPILED_DANGEROUS_PATTERNS:
        for i, line in enumerate(lines, 1):
            for match in pattern.finditer(line):
                match_start = line_starts[i - 1] + match.start()
                match_end = line_starts[i - 1] + match.end()
                if any(start <= match_start and match_end <= end
                       for start, end in masked_spans):
                    continue
                if (description in _DEFINITION_EXEMPT_DESCRIPTIONS
                        and _is_definition_site(line, match.start())):
                    continue
                findings.append(
                    f"{os.path.basename(filepath)}:{i}: "
                    f"检测到 {description}: `{line.strip()[:80]}`"
                )
    return findings
def content_label(ctx: OperationContext) -> str:
    target = (_pending_write_target(ctx) if _pending_code(ctx) is not None
              else target_path_str(ctx))
    return os.path.basename(target) or _DEFAULT_CONTENT_LABEL

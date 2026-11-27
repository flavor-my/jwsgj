from __future__ import annotations

import hashlib
import logging
import os
import re
import threading
import time
from collections import defaultdict
from collections.abc import Callable
from dataclasses import dataclass
from datetime import datetime
from typing import Any, ClassVar, Protocol

from jwsgj.build_import_reference import (
    _find_project_root as _find_reference_project_root,
)
from jwsgj.build_import_reference import (
    _path_identity,
    guard_blast_radius,
    guard_circular,
    guard_delete,
)
from jwsgj.build_import_time_guard import (
    guard_atexit_register,
    guard_import_side_effect,
    guard_imports,
)
from jwsgj.build_safe_rollback import (
    guard_rollback,
)
from jwsgj.build_safe_write import (
    _has_explicit_code_pair,
    file_backup,
    guard_backup,
    guard_path_sanitize,
    guard_post_verify,
    guard_safe_delete,
    guard_snapshot_diff,
)
from jwsgj.diag_guard_quality import (
    guard_ast,
    guard_concurrent_state,
    guard_dictret,
    guard_funcbody,
    guard_mro,
    guard_recursion_depth,
    guard_slots,
)
from jwsgj.diag_guard_source import (
    guard_content_diag,
    guard_docstring,
    guard_fstring,
    guard_size_limit,
    guard_syntax,
)
from jwsgj.diag_types_defs import (
    DEFAULT_OPERATION_AFFECTED_FILES,
    DEFAULT_OPERATION_DRY_RUN,
    DEFAULT_OPERATION_METADATA,
    DEFAULT_OPERATION_TARGET_PATH,
    GuardResult,
    OperationContext,
    common_parent_of,
    is_read_only_audit,
    issues_guard_result,
    metadata_path_str,
    normalize_operation_kind,
    normalize_target_path,
    target_path_str,
)
from jwsgj.diag_types_normalize import normalize_files_list
from jwsgj.diag_types_vocab import (
    MSG_EXCEPTION_BROAD_HANDLER,
    GuardLevel,
    OperationType,
)
from jwsgj.log_config import log_swallowed, perf_trace, write_audit

logger = logging.getLogger(__name__)
__all__ = [
    'COMMAND_BLACKLIST',
    'COMMAND_WHITELIST',
    'DEFAULT_EXECUTION_TIMEOUT_SEC',
    'DEFAULT_MAX_DELETE_OPERATIONS',
    'DEFAULT_MAX_FILE_OPERATIONS',
    'DEFAULT_PATH_WHITELIST',
    'DEFAULT_THROTTLE_DELAY_MS',
    'PATH_BLACKLIST',
    'SafeOpsOrchestrator',
    '_SessionState',
    'execute_single_guard',
    'get_guard_state',
    'get_registered_guards',
    'get_status',
    'guard_default_deny',
    'guard_diag_trail',
    'guard_idempotency',
    'guard_intent_confirm',
    'guard_throttle',
    'has_blockers',
    'install',
    'quick_report',
    'register_guard',
    'register_post_hook',
    'reset_guard_state',
    'run_guards',
    'run_post_hooks',
    'run_safe_ops_guards',
    'safe_delivery_check',
    'safe_postflight',
    'safe_preflight',
]
_GUARD_REGISTRY: dict = {}
_GUARD_STAGE_CHECK = "check"
_GUARD_STAGE_PREPARE = "prepare"
_GUARD_STAGES: dict[str, str] = {}
_GUARD_REGISTRY_LOCK = threading.RLock()
def register_guard(name: str, fn: Callable[[OperationContext], GuardResult],
                   *, stage: str | None = None) -> None:
    with _GUARD_REGISTRY_LOCK:
        _GUARD_REGISTRY[name] = fn
        if stage is None:
            _GUARD_STAGES.setdefault(name, _GUARD_STAGE_CHECK)
            return
        _GUARD_STAGES[name] = (_GUARD_STAGE_PREPARE
                               if stage == _GUARD_STAGE_PREPARE
                               else _GUARD_STAGE_CHECK)
def get_registered_guards() -> dict[str, Callable[[OperationContext], GuardResult]]:
    with _GUARD_REGISTRY_LOCK:
        return dict(_GUARD_REGISTRY)
def _empty_guard_stats() -> dict:
    return {"total_calls": 0, "guard_checks": 0, "pass_count": 0,
            "fail_count": 0, "block_count": 0, "skipped_prepare": 0,
            "history": [], "last_results": [], "per_guard": {}}
_GUARD_EXEC_STATS: dict = _empty_guard_stats()
_GUARD_STATS_LOCK = threading.Lock()
_GUARD_HISTORY_CAP = 1000
_GUARD_LAST_RESULTS_CAP = 20
def _record_one_guard_result(r: GuardResult, op_name: str) -> None:
    _GUARD_EXEC_STATS["guard_checks"] += 1
    blocked = _is_blocker(r)
    pg = _GUARD_EXEC_STATS["per_guard"].setdefault(
        r.guard_name, {"pass": 0, "fail": 0, "block": 0})
    if r.passed:
        _GUARD_EXEC_STATS["pass_count"] += 1
        pg["pass"] += 1
    else:
        _GUARD_EXEC_STATS["fail_count"] += 1
        pg["fail"] += 1
        if blocked:
            _GUARD_EXEC_STATS["block_count"] += 1
            pg["block"] += 1
    _GUARD_EXEC_STATS["history"].append({
        "guard": r.guard_name,
        "result": "pass" if r.passed else ("block" if blocked else "warn"),
        "level": r.level.value if r.level else None,
        "op_type": op_name,
        "message": (r.message or "")[:200],
    })
def _operation_name(ctx: OperationContext) -> str:
    operation = getattr(ctx, "operation", None)
    return str(getattr(operation, "value", operation) or "")
def _record_guard_exec(ctx: OperationContext, results: list[GuardResult]) -> None:
    op_name = _operation_name(ctx)
    with _GUARD_STATS_LOCK:
        _GUARD_EXEC_STATS["total_calls"] += 1
        for r in results:
            _record_one_guard_result(r, op_name)
        history = _GUARD_EXEC_STATS["history"]
        history[:] = history[-_GUARD_HISTORY_CAP:]
        _GUARD_EXEC_STATS["last_results"] = [
            {"guard": r.guard_name, "passed": r.passed,
             "level": r.level.value if r.level else None,
             "message": (r.message or "")[:200]}
            for r in results
        ][-_GUARD_LAST_RESULTS_CAP:]
def get_guard_state() -> dict:
    registered_count = len(get_registered_guards())
    with _GUARD_STATS_LOCK:
        total = _GUARD_EXEC_STATS["guard_checks"]
        block = _GUARD_EXEC_STATS["block_count"]
        return {
            "total_calls": _GUARD_EXEC_STATS["total_calls"],
            "guard_checks": total,
            "pass_count": _GUARD_EXEC_STATS["pass_count"],
            "fail_count": _GUARD_EXEC_STATS["fail_count"],
            "block_count": block,
            "skipped_prepare": _GUARD_EXEC_STATS["skipped_prepare"],
            "block_rate": round(block / total, 4) if total else 0.0,
            "registered_guards": registered_count,
            "history_size": len(_GUARD_EXEC_STATS["history"]),
            "last_results": [dict(item)
                             for item in _GUARD_EXEC_STATS["last_results"]],
            "per_guard": {k: dict(v) for k, v in _GUARD_EXEC_STATS["per_guard"].items()},
        }
def reset_guard_state() -> None:
    with _GUARD_STATS_LOCK:
        _GUARD_EXEC_STATS.update(_empty_guard_stats())
def _normalize_guard_names(
        names: list[str] | tuple[str, ...] | set[str] | str | None
) -> list[str] | None:
    if names is None:
        return None
    if isinstance(names, str):
        if not names.strip():
            logger.warning(
                "_normalize_guard_names: 空字符串名字无意义，按未指定处理，"
                "执行全部守卫（fail-closed）")
            return None
        return [names.strip()]
    try:
        raw_names = list(names)
    except TypeError as exc:
        logger.warning("_normalize_guard_names: names 不可迭代(%s)",
                       type(names).__name__)
        raise ValueError(
            f"守卫名集合类型非法（{type(names).__name__}），"
            "无法确认调用方请求的安全面") from exc
    if not raw_names:
        logger.warning(
            "_normalize_guard_names: 空守卫集合无法表达安全选择，"
            "按未指定处理，执行全部守卫（fail-closed）")
        return None
    valid_names = [name.strip() for name in raw_names
                   if isinstance(name, str) and name.strip()]
    invalid_count = len(raw_names) - len(valid_names)
    if invalid_count:
        logger.warning("_normalize_guard_names: 发现 %d 个非法或空守卫名",
                       invalid_count)
        raise ValueError(
            f"守卫名列表包含 {invalid_count} 个非法或空项，"
            "无法确认调用方请求的安全面")
    ordered: list[str] = []
    for name in valid_names:
        if name not in ordered:
            ordered.append(name)
    return ordered
def _blocked_guard_result(guard_name: str, message: str) -> GuardResult:
    return GuardResult(guard_name=guard_name, passed=False,
                       level=GuardLevel.BLOCK, message=message)
def execute_single_guard(name: str,
                         guard_fn: Callable[[OperationContext], GuardResult],
                         ctx: OperationContext) -> GuardResult:
    try:
        result = guard_fn(ctx)
    except Exception as e:
        logger.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
        return _blocked_guard_result(name, f"守卫执行异常: {e}")
    if not isinstance(result, GuardResult):
        logger.warning("run_guards: 守卫 %s 返回非 GuardResult(%s)，按 BLOCK 收敛",
                     name, type(result).__name__)
        return _blocked_guard_result(
            name,
            f"守卫返回非 GuardResult({type(result).__name__})，按阻断收敛")
    return result
def _ordered_guard_names(
        requested: list[str] | None) -> tuple[list[str], list[str]]:
    registered = list(_GUARD_REGISTRY)
    if requested is None:
        return registered, []
    registered_set = set(registered)
    order = [name for name in requested if name in registered_set]
    missing = [name for name in requested if name not in registered_set]
    return order, missing
def _split_by_stage(order: list[str]) -> tuple[list[str], list[str]]:
    checks = [name for name in order
              if _GUARD_STAGES.get(name, _GUARD_STAGE_CHECK)
              != _GUARD_STAGE_PREPARE]
    prepares = [name for name in order
                if _GUARD_STAGES.get(name, _GUARD_STAGE_CHECK)
                == _GUARD_STAGE_PREPARE]
    return checks, prepares
def _skip_prepare_guards(names: list[str], ctx: OperationContext) -> None:
    if not names:
        return
    logger.warning(
        "[run_guards] 前置守卫阻断，跳过准备阶段守卫 %s（op=%s target=%s）:"
        "被拒绝的操作不得落备份或占用配额",
        names, _operation_name(ctx), getattr(ctx, "target_path", "") or "")
    with _GUARD_STATS_LOCK:
        _GUARD_EXEC_STATS["skipped_prepare"] += len(names)
def _log_failed_round(results: list[GuardResult],
                       ctx: OperationContext) -> None:
    _failed = [r for r in results if not r.passed]
    if not _failed:
        return
    _blocked_n = sum(1 for r in _failed if _is_blocker(r))
    logger.warning(
        "[run_guards] %d/%d 守卫未通过(block=%d): %s | op=%s target=%s",
        len(_failed), len(results), _blocked_n,
        "; ".join(f"{r.guard_name}: {(r.message or '')[:60]}"
                  for r in _failed[:8]),
        _operation_name(ctx),
        getattr(ctx, "target_path", "") or "",
    )
def run_guards(ctx: OperationContext,
              names: list[str] | tuple[str, ...] | set[str] | str | None = None) -> list[GuardResult]:
    try:
        _names = _normalize_guard_names(names)
    except ValueError as exc:
        results = [_blocked_guard_result("run_guards", str(exc))]
        _log_failed_round(results, ctx)
        _record_guard_exec(ctx, results)
        return results
    with _GUARD_REGISTRY_LOCK:
        order, _missing = _ordered_guard_names(_names)
        if isinstance(names, (set, frozenset)):
            registry_index = {name: i for i, name in enumerate(_GUARD_REGISTRY)}
            order.sort(key=registry_index.__getitem__)
        checks, prepares = _split_by_stage(order)
        guard_fns = {name: _GUARD_REGISTRY[name] for name in order}
    results = [execute_single_guard(name, guard_fns[name], ctx)
               for name in checks]
    blocked = any(_is_blocker(result) for result in results)
    if _missing:
        logger.warning("run_guards: 请求的守卫未注册，按阻断收敛: %s", _missing)
        blocked = True
    if blocked:
        _skip_prepare_guards(prepares, ctx)
    else:
        for index, name in enumerate(prepares):
            result = execute_single_guard(name, guard_fns[name], ctx)
            results.append(result)
            if _is_blocker(result):
                _skip_prepare_guards(prepares[index + 1:], ctx)
                break
    results.extend(
        _blocked_guard_result(
            name, f"请求的守卫 {name} 未注册，无法确认安全面，按阻断收敛")
        for name in _missing
    )
    if not results:
        results.append(_blocked_guard_result(
            "run_guards", "未执行任何守卫，无法确认安全面，按阻断收敛"))
    _log_failed_round(results, ctx)
    _record_guard_exec(ctx, results)
    return results
DEFAULT_PATH_WHITELIST: set[str] = {
    "workspace", "output", "skills",
    "Documents", "Desktop", "Downloads",
}
def _find_project_root(target_path: str) -> str:
    try:
        current = os.path.realpath(os.path.abspath(target_path))
    except (OSError, ValueError) as _swallowed_exc:
        log_swallowed(__name__, _swallowed_exc,
                      context=f'_find_project_root:{type(_swallowed_exc).__name__}')
        return ""
    if not os.path.isdir(current):
        current = os.path.dirname(current)
    return _find_reference_project_root(current)
_ALLOWED_ROOTS_ENV = "SAFE_OPS_ALLOWED_ROOTS"
_ALLOWED_COMMANDS_ENV = "SAFE_OPS_ALLOWED_COMMANDS"
PATH_BLACKLIST: set[str] = {
    "/etc", "/System", "/Windows", "/root", "/usr/bin",
    "/bin", "/sbin", "/boot", "/sys", "/proc", "/dev",
    ".env", ".ssh", "id_rsa", "authorized_keys",
    "known_hosts", ".gitconfig", ".bashrc", ".zshrc",
    ".npmrc", ".pypirc", "credentials", "secrets",
}
COMMAND_WHITELIST: set[str] = {
    "ls", "dir", "cd", "cat", "echo", "grep", "find", "head", "tail",
    "wc", "sort", "uniq", "cut", "awk", "sed",
    "python", "python3", "pip", "pip3", "node", "npm", "npx",
    "git", "tar", "zip", "unzip", "curl", "wget",
    "mkdir", "rmdir", "cp", "mv",
    "docker", "ps", "kill",
    "pytest", "ruff", "mypy", "pyright", "black", "isort",
    "flake8", "pylint", "bandit", "coverage", "tox", "nox",
    "uv", "poetry", "pdm", "hatch", "pre-commit", "make",
}
COMMAND_BLACKLIST: set[str] = {
    "rm -rf", "rm -r", "sudo rm", "chmod 777", "chmod -R",
    "mkfs", "dd if=", "format", "shutdown", "reboot",
    "regedit", "del /f", "rd /s",
}
def _string_list(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if value.strip() else []
    if isinstance(value, (list, tuple, set, frozenset)):
        return [item.strip() for item in value
                if isinstance(item, str) and item.strip()]
    return []
def _env_string_list(name: str) -> list[str]:
    raw = os.environ.get(name, "")
    if not isinstance(raw, str) or not raw.strip():
        return []
    return [item.strip() for item in raw.split(os.pathsep) if item.strip()]
def _configured_allowed_roots(metadata: Any) -> list[str]:
    meta = metadata if isinstance(metadata, dict) else {}
    return (_string_list(meta.get("allowed_roots"))
            + _env_string_list(_ALLOWED_ROOTS_ENV))
def _configured_allowed_commands(metadata: Any) -> list[str]:
    meta = metadata if isinstance(metadata, dict) else {}
    return (_string_list(meta.get("allowed_commands"))
            + _env_string_list(_ALLOWED_COMMANDS_ENV))
def _path_text(value) -> str | None:
    if isinstance(value, str):
        return value
    if value is None or isinstance(value, bool):
        return None
    if isinstance(value, (bytes, bytearray)):
        try:
            return bytes(value).decode("utf-8")
        except UnicodeDecodeError as _e:
            log_swallowed(__name__, _e, context='_path_text:UnicodeDecodeError')
            return None
    try:
        raw = os.fspath(value)
    except TypeError:
        return None
    return _path_text(raw)
def _canonical_path_parts(target_path: str) -> list[str]:
    try:
        norm = os.path.normcase(os.path.realpath(os.path.abspath(target_path)))
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_canonical_path_parts:{type(_e).__name__}')
        return []
    norm = norm.replace("\\", "/")
    if os.name == "nt":
        norm = re.sub(r"^//[.?]/(?=[a-z]:/)", "", norm, count=1)
    return [part for part in norm.split("/") if part]
def _path_under_roots(target_path: str, roots: list[str]) -> bool:
    target_parts = _canonical_path_parts(target_path)
    for root in roots:
        root_parts = _canonical_path_parts(root)
        if root_parts and target_parts[:len(root_parts)] == root_parts:
            return True
    return False
def _check_path_whitelist(target_path, include_whitelist: bool = True,
                          allowed_roots: list[str] | None = None) -> list[str]:
    issues: list[str] = []
    text = _path_text(target_path)
    if text is None:
        return [(f"路径通道类型非法（{type(target_path).__name__}），"
                 "无法归一为可校验路径，操作被默认拒绝.")]
    if not text:
        return issues
    lowered_parts, parts_no_drive = _normalized_path_parts(text)
    hit = _path_blacklist_hit(lowered_parts, parts_no_drive)
    if hit is not None:
        issues.append(
            f"路径 {text} 命中敏感路径黑名单: {hit}."
            f"操作被默认拒绝."
        )
        return issues
    if not include_whitelist:
        return issues
    roots = list(allowed_roots or ())
    authorized = (_path_in_whitelist(text)
                  or _path_under_roots(text, roots)
                  or bool(_find_project_root(text)))
    if not authorized:
        extra = ""
        if roots:
            extra = f" 额外允许根: {', '.join(sorted(roots))}."
        issues.append(
            f"路径 {text} 不在白名单内."
            f"白名单: {', '.join(sorted(DEFAULT_PATH_WHITELIST))}."
            f"{extra}操作被默认拒绝."
        )
    return issues
def _normalized_path_parts(target_path: str) -> tuple[list[str], list[str]]:
    lowered_parts = [part.lower() for part in _canonical_path_parts(target_path)]
    if os.name == "nt":
        lowered_parts = [
            part if re.fullmatch(r"[a-z]:", part)
            else part.split(":", 1)[0]
            for part in lowered_parts
        ]
    drive_index: int | None = None
    if lowered_parts and re.fullmatch(r"[a-z]:", lowered_parts[0]):
        drive_index = 0
    elif (len(lowered_parts) >= 2
          and re.fullmatch(r"[a-z]\$", lowered_parts[1])):
        drive_index = 1
    elif (len(lowered_parts) >= 4
          and lowered_parts[0] in ("?", ".")
          and lowered_parts[1] == "unc"
          and re.fullmatch(r"[a-z]\$", lowered_parts[3])):
        drive_index = 3
    parts_no_drive = (lowered_parts[drive_index + 1:]
                      if drive_index is not None else lowered_parts)
    return lowered_parts, parts_no_drive
def _path_blacklist_hit(lowered_parts: list[str],
                        parts_no_drive: list[str]) -> str | None:
    for black in sorted(PATH_BLACKLIST, key=lambda e: (-len(e), e)):
        if black.startswith("/"):
            seq = [seg.lower() for seg in black.split("/") if seg]
            if seq and parts_no_drive[:len(seq)] == seq:
                return black
        elif black.lower() in lowered_parts:
            return black
    return None
def _path_in_whitelist(target_path: str) -> bool:
    parts = [part.lower() for part in _canonical_path_parts(target_path)]
    return any(white.lower() in parts for white in DEFAULT_PATH_WHITELIST)
_SHELL_WORD_PATTERN = (r"[^\s;&|<>]*" if os.name == "nt"
                       else r"(?:\\.|[^\s;&|<>])*")
def _is_shell_quote_char(ch: str) -> bool:
    return ch == '"' or (ch == "'" and os.name != "nt")
_REDIRECT_OPERATOR_PATTERN = (
    r"(?:\d+\s*)?(?:>>|>\||<>|[<>]&|[<>])|&>>?"
)
_REDIRECT_TARGET_PATTERN = rf"&\s*\d+|{_SHELL_WORD_PATTERN}"
_REDIRECT_TOKEN_RE = re.compile(  # jwsgj:suppress SE-30 — 线性词元原子覆盖转义字符，无嵌套量词回溯
    rf"(?:{_REDIRECT_OPERATOR_PATTERN})\s*"
    rf"(?:{_REDIRECT_TARGET_PATTERN})"
)
_FORK_BOMB_RE = re.compile(
    r":\s*\(\s*\)\s*\{[^}]*:\s*\|\s*:\s*&\s*\}\s*;\s*:")
_ENV_ASSIGN_TOKEN_RE = re.compile(r"[A-Za-z_]\w*=")
_WINDOWS_PERCENT_EXPANSION_RE = re.compile(r"%[^%\s]+%")
_QUOTED_SPAN_RE = re.compile(r"\x01(\d+)\x02")
_SHELL_SEPARATOR_RE = re.compile(r"\s*(?:&&|\|\||[;|&\n])\s*")
_FIND_DESTRUCTIVE_FLAGS = frozenset(
    {"-exec", "-execdir", "-ok", "-okdir", "-delete"})
def _mask_quoted_spans(text: str) -> tuple[str, list[str]]:
    masked: list[str] = []
    spans: list[str] = []
    plain_start = 0
    pos = 0
    while pos < len(text):
        if os.name != "nt" and text[pos] == "\\":
            # POSIX 非引号上下文中，反斜杠转义下一字符；被转义的引号不构成边界。
            pos += 2
            continue
        if os.name == "nt" and text[pos] == "^":
            # CMD 脱字符转义下一字符（含引号）：^" 是字面引号而非引用边界，
            # 否则分隔符会被后续配对引号吞掉，隐藏真实执行的命令。
            pos += 2
            continue
        quote = text[pos]
        if not _is_shell_quote_char(quote):
            pos += 1
            continue
        end = pos + 1
        while end < len(text):
            if (text[end] == "\\" and quote == '"'
                    and os.name != "nt"):
                end += 2
                continue
            if text[end] == quote:
                break
            end += 1
        if end >= len(text):
            break
        masked.append(text[plain_start:pos])
        spans.append(text[pos:end + 1])
        masked.append(f"\x01{len(spans) - 1}\x02")
        pos = end + 1
        plain_start = pos
    masked.append(text[plain_start:])
    return "".join(masked), spans
def _restore_quoted_spans(text: str, spans: list[str]) -> str:
    def _replace(match: re.Match[str]) -> str:
        index = int(match.group(1))
        return spans[index] if index < len(spans) else match.group(0)
    return _QUOTED_SPAN_RE.sub(_replace, text)
def _consume_quoted_shell_char(ch: str, quote: str, escaped: bool,
                               buf: list[str]) -> tuple[str, bool]:
    if escaped:
        buf.append(ch)
        return quote, False
    if quote == '"' and ch == "\\" and os.name != "nt":
        return quote, True
    if ch == quote:
        return "", False
    buf.append(ch)
    return quote, False
def _consume_unquoted_shell_char(ch: str, buf: list[str]) -> tuple[str, bool]:
    if _is_shell_quote_char(ch):
        return ch, False
    if ch.isspace():
        return "", True
    buf.append(ch)
    return "", False
def _shell_tokens(segment: str) -> list[str]:
    tokens: list[str] = []
    buf: list[str] = []
    quote = ""
    escaped = False
    for ch in segment:
        if quote:
            quote, escaped = _consume_quoted_shell_char(
                ch, quote, escaped, buf)
            continue
        if escaped:
            buf.append(ch)
            escaped = False
            continue
        if ch == "\\" and os.name != "nt":
            escaped = True
            continue
        if ch == "^" and os.name == "nt":
            # CMD 脱字符：非引号上下文中 ^x 传递字面 x（如 ^/s 等价 /s，
            # 字面 ^ 需写成 ^^）；不归一会被递归删除/黑名单检测绕过。
            escaped = True
            continue
        quote, end_token = _consume_unquoted_shell_char(ch, buf)
        if end_token and buf:
            tokens.append("".join(buf))
            buf = []
    if escaped:
        buf.append("^" if os.name == "nt" else "\\")
    if buf:
        tokens.append("".join(buf))
    return tokens
def _masked_command_parts(command: str) -> list[str]:
    masked, spans = _mask_quoted_spans(command)
    stripped = _REDIRECT_TOKEN_RE.sub(" ", masked)
    return [_restore_quoted_spans(seg, spans)
            for seg in _SHELL_SEPARATOR_RE.split(stripped) if seg.strip()]
def _quoted_shell_step(command: str, pos: int,
                       quote: str) -> tuple[int, str, str | None]:
    ch = command[pos]
    if quote == "'":
        return pos + 1, "" if ch == "'" else quote, None
    if ch == "\\":
        return pos + 2, quote, None
    if ch == '"':
        return pos + 1, "", None
    if ch == "`" or command.startswith("$(", pos):
        return pos + 1, quote, "命令替换"
    return pos + 1, quote, None
def _unquoted_shell_step(command: str,
                         pos: int) -> tuple[int, str, str | None]:
    ch = command[pos]
    if ch in ("'", '"'):
        return pos + 1, ch, None
    if ch == "\\":
        return pos + 2, "", None
    if ch == "`" or command.startswith("$(", pos):
        return pos + 1, "", "命令替换"
    if command.startswith("<(", pos) or command.startswith(">(", pos):
        return pos + 1, "", "进程替换"
    return pos + 1, "", None
def _shell_substitution_construct(command: str) -> str | None:
    quote = ""
    pos = 0
    while pos < len(command):
        if quote:
            pos, quote, unsafe = _quoted_shell_step(command, pos, quote)
        else:
            pos, quote, unsafe = _unquoted_shell_step(command, pos)
        if unsafe is not None:
            return unsafe
    return None
def _command_start_index(tokens: list[str]) -> int:
    index = 0
    while (index < len(tokens)
           and _ENV_ASSIGN_TOKEN_RE.match(tokens[index])):
        index += 1
    return index
def _find_exec_construct(command: str) -> str | None:
    for segment in _masked_command_parts(command):
        tokens = _shell_tokens(segment)
        index = _command_start_index(tokens)
        if (index < len(tokens) and tokens[index].lower() == "find"
                and any(token.lower() in _FIND_DESTRUCTIVE_FLAGS
                        for token in tokens[index + 1:])):
            return "find 的 -exec/-ok/-delete"
    return None
def _unsafe_shell_construct(command: str) -> str | None:
    if os.name == "nt" and _WINDOWS_PERCENT_EXPANSION_RE.search(command):
        return "Windows 环境变量展开"
    return (_shell_substitution_construct(command)
            or _find_exec_construct(command))
def _check_command_whitelist(command: Any,
                             extra_whitelist: list[str] | None = None
                             ) -> list[str]:
    if not isinstance(command, str):
        return [(f"命令通道类型非法（{type(command).__name__}），"
                 "静态白名单无法校验其实际执行内容，操作被默认拒绝.")]
    if _FORK_BOMB_RE.search(command):
        return [(f"命令 '{command[:60]}' 命中 fork 炸弹结构（递归自管道），"
                 "操作被默认拒绝.")]
    unsafe = _unsafe_shell_construct(command)
    if unsafe is not None:
        return [(f"命令 '{command[:60]}' 含 {unsafe} 结构，"
                 "静态白名单无法校验其实际执行内容，操作被默认拒绝.")]
    segments = _masked_command_parts(command)
    seg_names = _command_position_names(segments)
    seg_names_lower = [name.lower() for name in seg_names]
    hit = _command_blacklist_hit(segments, seg_names_lower)
    if hit is not None:
        return [(f"命令 '{command[:60]}' 命中高危命令黑名单: {hit}."
                 f"操作被默认拒绝.")]
    if not seg_names:
        return [(f"命令 '{command[:60]}' 未包含可执行命令."
                 "操作被默认拒绝.")]
    return _whitelist_rejections(seg_names, seg_names_lower, extra_whitelist)
def _command_position_names(segments: list[str]) -> list[str]:
    seg_names: list[str] = []
    for seg in segments:
        tokens = _shell_tokens(seg)
        cmd_idx = _command_start_index(tokens)
        if cmd_idx < len(tokens):
            seg_names.append(tokens[cmd_idx])
    return seg_names
def _whitelist_rejections(seg_names: list[str],
                          seg_names_lower: list[str],
                          extra_whitelist: list[str] | None = None
                          ) -> list[str]:
    base_lower = {white.lower() for white in COMMAND_WHITELIST}
    extra_lower = {white.lower() for white in (extra_whitelist or ())
                   if isinstance(white, str) and white}
    whitelist_lower = base_lower | extra_lower
    extra_text = ""
    if extra_lower - base_lower:
        extra_text = (" 额外允许: "
                      + ", ".join(sorted(extra_lower - base_lower)) + ".")
    return [f"命令 '{seg_name}' 不在白名单内."
            f"白名单: {', '.join(sorted(COMMAND_WHITELIST))}."
            f"{extra_text}操作被默认拒绝."
            for seg_name, seg_name_l in zip(seg_names, seg_names_lower,
                                            strict=True)
            if seg_name_l not in whitelist_lower]
def _blacklist_prefix_matches(tokens: list[str], expected: list[str]) -> bool:
    if len(tokens) < len(expected):
        return False
    for actual, wanted in zip(tokens, expected, strict=False):
        actual_lower = actual.lower()
        wanted_lower = wanted.lower()
        if wanted_lower.endswith("="):
            if not actual_lower.startswith(wanted_lower):
                return False
        elif actual_lower != wanted_lower:
            return False
    return True
_RECURSIVE_DELETE_RULE = "rd /s"
_RECURSIVE_DELETE_ALIASES = frozenset({"rd", "rmdir"})
def _recursive_delete_hit(command_tokens: list[str]) -> bool:
    # Windows 的 rd/rmdir 是同一内置命令：/s 即递归删除（等价 rm -rf），且开关顺序任意；
    # rmdir 因 POSIX 语义（仅删空目录）在白名单内，必须按 /s 开关而非字面前缀识别。
    if (not command_tokens
            or command_tokens[0].lower() not in _RECURSIVE_DELETE_ALIASES):
        return False
    return any(token.lower() == "/s" for token in command_tokens[1:])
def _command_blacklist_hit(segments: list[str],
                           seg_names_lower: list[str]) -> str | None:
    for black in sorted(COMMAND_BLACKLIST, key=lambda e: (-len(e), e)):
        if " " not in black:
            if black.lower() in seg_names_lower:
                return black
            continue
        expected = black.split(" ")
        for segment in segments:
            tokens = _shell_tokens(segment)
            command_tokens = tokens[_command_start_index(tokens):]
            if _blacklist_prefix_matches(command_tokens, expected):
                return black
    for segment in segments:
        tokens = _shell_tokens(segment)
        if _recursive_delete_hit(tokens[_command_start_index(tokens):]):
            return _RECURSIVE_DELETE_RULE
    return None
_REDIRECT_TARGET_RE = re.compile(
    rf"(?P<operator>{_REDIRECT_OPERATOR_PATTERN})\s*"
    rf"(?P<target>{_REDIRECT_TARGET_PATTERN})")
_BENIGN_REDIRECT_TARGETS = frozenset(
    {os.devnull.lower()}
    if os.name == "nt"
    else {os.devnull.lower(), "/dev/null", "/dev/stdout", "/dev/stderr",
          "/dev/tty"}
)
def _command_redirect_targets(command: str) -> list[str]:
    masked, spans = _mask_quoted_spans(command)
    targets: list[str] = []
    for match in _REDIRECT_TARGET_RE.finditer(masked):
        raw = match.group("target")
        operator = match.group("operator")
        if not raw:
            continue
        if (re.search(r"[<>]&$", operator)
                and re.fullmatch(r"\d+|-", raw)):
            continue
        if raw.lstrip().startswith("&"):
            continue
        restored = _restore_quoted_spans(raw, spans)
        target = "".join(_shell_tokens(restored))
        if not target or target.lower() in _BENIGN_REDIRECT_TARGETS:
            continue
        targets.append(restored)
    return targets
def _redirect_target_expansion(raw: str) -> str | None:
    if (_WINDOWS_PERCENT_EXPANSION_RE.search(raw)
            or re.search(r"![^!\s]+!", raw)):
        return "Windows 环境变量/延迟展开"
    quote = ""
    pos = 0
    literal_seen = False
    while pos < len(raw):
        ch = raw[pos]
        if os.name == "nt" and ch == "^" and not quote:
            end = pos
            while end < len(raw) and raw[end] == "^":
                end += 1
            if end == len(raw):
                if (end - pos) % 2:
                    return "CMD 转义/续行"
                pos = end
                literal_seen = True
                continue
        if quote == "'":
            if ch == "'":
                quote = ""
            pos += 1
            continue
        if ch == "\\":
            literal_seen = True
            pos += 2
            continue
        if quote and ch == quote:
            quote = ""
            literal_seen = True
            pos += 1
            continue
        if not quote and ch in ("'", '"'):
            quote = ch
            literal_seen = True
            pos += 1
            continue
        if ch == "$" and pos + 1 < len(raw):
            following = raw[pos + 1]
            if (following in "({['\"" or following.isalnum()
                    or following in "_?@#*$!-"):
                return "shell 变量/算术/特殊引用展开"
        # 引号外（且未被反斜杠或 ^ 转义）的通配符/花括号会让 shell 按已有文件名
        # 改写目标词（如 `.en*` → `.env`、`*.py` → cwd 唯一 .py），静态白名单
        # 校验的是字面词而非实际写入位置，必须按展开拒绝；引号内为字面文件名不报。
        if not quote and ch in "*?[{":
            return "shell 通配符/花括号展开"
        if ch == "~" and not quote and not literal_seen:
            return "shell 用户目录展开"
        literal_seen = True
        pos += 1
    return None
def _redirect_target_path(raw_target: str) -> str:
    literal: list[str] = []
    quote = ""
    pos = 0
    while pos < len(raw_target):
        ch = raw_target[pos]
        if (os.name == "nt" and ch == "^" and not quote
                and pos + 1 < len(raw_target)):
            pos += 1
            literal.append(raw_target[pos])
        elif quote:
            if ch == quote:
                quote = ""
            else:
                literal.append(ch)
        elif ch in ("'", '"'):
            quote = ch
        else:
            literal.append(ch)
        pos += 1
    windows_path = re.sub(r"\\(?=\s)", "", "".join(literal))
    if (os.name == "nt"
            or re.match(r"^(?:[A-Za-z]:|\\\\|//)", windows_path)):
        return windows_path
    return "".join(_shell_tokens(raw_target))
def _command_path_issues(
        command: str, allowed_roots: list[str] | None = None) -> list[str]:
    issues: list[str] = []
    for raw_target in _command_redirect_targets(command):
        expansion = _redirect_target_expansion(raw_target)
        if expansion is not None:
            issues.append(
                f"命令重定向目标 {raw_target} 含 {expansion}，"
                "静态白名单无法确认实际写入位置，操作被默认拒绝.")
            continue
        target = _redirect_target_path(raw_target)
        for issue in _check_path_whitelist(target, allowed_roots=allowed_roots):
            issues.append(f"命令重定向目标: {issue}")
    return issues
_DELETE_OPS = frozenset({OperationType.DELETE_FILE, OperationType.DELETE_DIR})
_DELETE_OP_NAMES = frozenset(op.value for op in _DELETE_OPS)
_MODIFY_OPS = frozenset({OperationType.MODIFY_CODE, OperationType.REFACTOR})
_RELOCATE_OPS = (OperationType.RENAME, OperationType.MOVE)
_WRITE_SCOPE_OPS = _DELETE_OPS | _MODIFY_OPS | {OperationType.CLEANUP}
_G13_WL_OPS = frozenset({
    *_DELETE_OPS, *_MODIFY_OPS, OperationType.CLEANUP,
    OperationType.WRITE_FILE, OperationType.RENAME,
    OperationType.MERGE, OperationType.MOVE,
    OperationType.ADD_IMPORT, OperationType.REMOVE_CODE, OperationType.SPLIT,
})
def _relocate_destination_issues(ctx: OperationContext,
                                 allowed_roots: list[str]) -> list[str]:
    raw_new_path = ctx.metadata.get("new_path", "")
    new_path = metadata_path_str(ctx, "new_path")
    if new_path:
        return _check_path_whitelist(new_path, allowed_roots=allowed_roots)
    if raw_new_path:
        return [(f"重命名目的地类型非法（{type(raw_new_path).__name__}），"
                 "无法校验目标路径.操作被默认拒绝.")]
    return [("重命名/移动操作缺少目的地（metadata.new_path 为空），"
             "无法校验目标路径.操作被默认拒绝.")]
def _g13_path_issues(
        ctx: OperationContext, allowed_roots: list[str]) -> list[str]:
    issues: list[str] = []
    if ctx.operation in _G13_WL_OPS:
        if (not target_path_str(ctx)
                and not normalize_files_list(ctx.affected_files)):
            issues.append(
                "写操作缺少 target_path 与 affected_files，"
                "无法确认默认拒绝边界，操作被默认拒绝.")
        issues.extend(_check_path_whitelist(
            ctx.target_path, allowed_roots=allowed_roots))
        if ctx.operation in _RELOCATE_OPS:
            issues.extend(_relocate_destination_issues(ctx, allowed_roots))
    for fpath in normalize_files_list(ctx.affected_files):
        issues.extend(_check_path_whitelist(
            fpath, include_whitelist=ctx.operation in _G13_WL_OPS,
            allowed_roots=allowed_roots))
    return issues
def _command_metadata_issues(metadata: Any) -> list[str]:
    if not hasattr(metadata, "get"):
        return []
    raw = metadata.get("command")
    if raw is None or isinstance(raw, str):
        return []
    return [(f"命令通道类型非法（{type(raw).__name__}），"
             "静态白名单无法校验其实际执行内容，操作被默认拒绝.")]
def guard_default_deny(ctx: OperationContext) -> GuardResult:
    operation = normalize_operation_kind(getattr(ctx, "operation", None))
    if not isinstance(operation, OperationType):
        return GuardResult(
            guard_name="G13", passed=False, level=GuardLevel.BLOCK,
            message=f"无效操作类型: {operation!r}，无法确定安全面，按阻断收敛",
            fix_suggestion="传入 OperationType 枚举或其合法字符串值")
    if is_read_only_audit(ctx):
        return GuardResult(guard_name="G13", passed=True,
                           message="只读审计,跳过默认拒绝检查（无真实写操作）")
    allowed_roots = _configured_allowed_roots(ctx.metadata)
    issues: list[str] = _g13_path_issues(ctx, allowed_roots)
    issues.extend(_command_metadata_issues(ctx.metadata))
    command = ctx.metadata.get("command", "")
    if isinstance(command, str) and command:
        cmd_issues = _check_command_whitelist(
            command, _configured_allowed_commands(ctx.metadata))
        issues.extend(cmd_issues)
        issues.extend(_command_path_issues(command, allowed_roots))
    return issues_guard_result(
        "G13", "默认拒绝检查", "违规", issues,
        "将目标路径加入白名单,或使用白名单内的命令."
        "默认拒绝原则:不在白名单内的一律拒绝.",
        "默认拒绝检查通过")
_DEFAULT_TASK_TYPE = 'default'
_SAFE_GUARD_NAMES: tuple[str, ...] = ("G1", "G5", "G20", "G23", "G24")
def run_safe_ops_guards(
        operation: OperationType | str,
        target_path: str = DEFAULT_OPERATION_TARGET_PATH,
        dry_run: bool = DEFAULT_OPERATION_DRY_RUN,
        metadata: dict | None = DEFAULT_OPERATION_METADATA,
        affected_files: list[str] | None = DEFAULT_OPERATION_AFFECTED_FILES,
) -> list[GuardResult]:
    try:
        op = (operation if isinstance(operation, OperationType)
              else OperationType(operation))
    except ValueError as _e:
        logger.warning("[SafeOps] 无效操作类型 %r: %s", operation, _e)
        return [GuardResult(
            guard_name="run_safe_ops_guards", passed=False,
            level=GuardLevel.BLOCK,
            message=f"无效操作类型: {operation!r}，"
                    f"支持值: {[m.value for m in OperationType]}",
            fix_suggestion="传入 OperationType 枚举或其合法字符串值"
                           "（如 'modify_code'）",
        )]
    ctx = OperationContext(
        operation=op, target_path=target_path, affected_files=affected_files,
        metadata=metadata, dry_run=dry_run)
    return run_guards(ctx, _SAFE_GUARD_NAMES)
_TASK_TO_OPERATION: dict[str, OperationType] = {
    member.value: member for member in OperationType
}
_TASK_TO_OPERATION.update({
    "script": OperationType.MODIFY_CODE,
    "review": OperationType.MODIFY_CODE,
    "delete": OperationType.DELETE_FILE,
    _DEFAULT_TASK_TYPE: OperationType.MODIFY_CODE,
})
def _normalize_task_type(task_type: Any) -> str:
    if isinstance(task_type, OperationType):
        task = task_type.value
    elif isinstance(task_type, str):
        task = task_type
    else:
        raise ValueError(
            f"无效任务类型: {task_type!r}，类型必须是字符串或 OperationType")
    if task not in _TASK_TO_OPERATION:
        raise ValueError(
            f"无效任务类型: {task!r}，支持值: {sorted(_TASK_TO_OPERATION)}")
    return task
class _SyntaxVerdictCache(Protocol):
    def flush_syntax_verdicts(self) -> None: ...
def _is_blocker(result: GuardResult) -> bool:
    return (not result.passed) and result.level == GuardLevel.BLOCK
def _result_counts(results: list[GuardResult]) -> tuple[int, int, int]:
    passed = blockers = warnings = 0
    for result in results:
        if result.passed:
            passed += 1
        elif _is_blocker(result):
            blockers += 1
        else:
            warnings += 1
    return passed, blockers, warnings
def _verdict_payload(results: list[GuardResult]) -> dict[str, Any]:
    passed, blockers, warnings = _result_counts(results)
    blocked = blockers > 0
    return {'ok': not blocked, 'blocked': blocked,
            'passed': passed, 'failed': len(results) - passed,
            'warnings': warnings, 'blockers': blockers,
            'total': len(results),
            'issues': _issues_payload(results),
            'report': quick_report(results)}
def safe_delivery_check(
        target_path: str = DEFAULT_OPERATION_TARGET_PATH,
        affected_files: list[str] | None = DEFAULT_OPERATION_AFFECTED_FILES,
        cache: _SyntaxVerdictCache | None = None) -> dict[str, Any]:
    files = list(normalize_files_list(affected_files))
    if not normalize_target_path(target_path) and not files:
        return _verdict_payload([_blocked_guard_result(
            "safe_delivery_check",
            "未提供交付目标（target_path 与 affected_files 均为空），"
            "无法确认安全面，按阻断收敛")])
    _metadata: dict = {'reason': '交付前全量检查', 'read_only_audit': True}
    if cache is not None:
        _metadata['shared_cache'] = cache
    ctx = OperationContext(
        operation=OperationType.REFACTOR, target_path=target_path,
        affected_files=files, metadata=_metadata)
    if not target_path_str(ctx):
        return _verdict_payload([_blocked_guard_result(
            "safe_delivery_check",
            "交付文件无法确定共同父目录，无法确认安全面，按阻断收敛")])
    all_results = run_guards(ctx)
    _flush = getattr(cache, 'flush_syntax_verdicts', None)
    if callable(_flush):
        try:
            _flush()
        except Exception:
            logger.debug('flush_syntax_verdicts failed', exc_info=True)
    return _verdict_payload(all_results)
def _issues_payload(results: list[GuardResult]) -> list[dict[str, Any]]:
    return [{'guard': r.guard_name,
             'level': r.level.value if r.level else None,
             'message': r.message or '',
             'details': list(getattr(r, 'details', []) or [])}
            for r in results if not r.passed]
def has_blockers(results: list[GuardResult]) -> bool:
    return any(map(_is_blocker, results))
def quick_report(results: list[GuardResult]) -> str:
    lines = [f'SafeOps Report: {len(results)} guards checked']
    for r in results:
        status = 'PASS' if r.passed else 'FAIL'
        lines.append(f'  [{r.guard_name}] {status}: {r.message}')
        if r.fix_suggestion:
            lines.append(f'         Fix: {r.fix_suggestion}')
    passed, blocked, warnings = _result_counts(results)
    summary = f'  Summary: {passed}/{len(results)} passed, {blocked} blocked'
    if warnings:
        summary += f', {warnings} warned'
    lines.append(summary)
    return '\n'.join(lines)
def _build_task_context(task_type: Any, target_path: Any,
                        affected_files: Any, metadata: Any) -> OperationContext:
    task = _normalize_task_type(task_type)
    ctx = OperationContext(
        operation=_TASK_TO_OPERATION[task],
        target_path=target_path, affected_files=affected_files,
        metadata=metadata)
    ctx.metadata['task_type'] = task
    return ctx
_PREFLIGHT_GUARDS: tuple[str, ...] = (
    'G19', 'G20', 'G13', 'G1', 'G5', 'G16', 'G15', 'G26', 'G18', 'G22')
_POSTFLIGHT_GUARDS: tuple[str, ...] = (
    'G2', 'G3', 'G4', 'G21', 'G23', 'G6', 'G7', 'G8', 'G9', 'G14',
    'G17', 'G24', 'G25', 'G27', 'G28', 'G29')
_DELIVERY_ONLY_GUARDS: tuple[str, ...] = ('G10', 'G11', 'G12')
def safe_preflight(
        task_type: str | OperationType = _DEFAULT_TASK_TYPE,
        target_path: str = DEFAULT_OPERATION_TARGET_PATH,
        affected_files: list[str] | None = DEFAULT_OPERATION_AFFECTED_FILES,
        metadata: dict[str, Any] | None = DEFAULT_OPERATION_METADATA,
) -> dict[str, Any]:
    try:
        ctx = _build_task_context(
            task_type, target_path, affected_files, metadata)
    except ValueError as exc:
        logger.warning("[SafeOps] preflight 参数无效: %s", exc)
        return _verdict_payload([_blocked_guard_result(
            "safe_preflight", str(exc))])
    relevant = run_guards(ctx, _PREFLIGHT_GUARDS)
    return _verdict_payload(relevant)
def safe_postflight(
        task_type: str | OperationType = _DEFAULT_TASK_TYPE,
        target_path: str = DEFAULT_OPERATION_TARGET_PATH,
        affected_files: list[str] | None = DEFAULT_OPERATION_AFFECTED_FILES,
        before_code: str = '', after_code: str = '',
        metadata: dict[str, Any] | None = DEFAULT_OPERATION_METADATA,
) -> dict[str, Any]:
    try:
        ctx = _build_task_context(
            task_type, target_path, affected_files, metadata)
    except ValueError as exc:
        logger.warning("[SafeOps] postflight 参数无效: %s", exc)
        return _verdict_payload([_blocked_guard_result(
            "safe_postflight", str(exc))])
    ctx.metadata['before_code'] = before_code
    ctx.metadata['after_code'] = after_code
    if (isinstance(after_code, str)
            and (after_code or _has_explicit_code_pair(before_code, after_code))):
        ctx.metadata['code_to_write'] = after_code
    relevant = run_guards(ctx, _POSTFLIGHT_GUARDS)
    return _verdict_payload(relevant)
_POST_HOOKS: list[Callable[[Any], dict]] = []
_POST_HOOKS_LOCK = threading.RLock()
_INSTALLED = False
def _hook_name(fn: Callable[[Any], dict]) -> str:
    return getattr(fn, '__name__', str(fn))
def register_post_hook(fn: Callable[[Any], dict]) -> None:
    if not callable(fn):
        raise TypeError(f'钩子必须是可调用对象, got {type(fn)}')
    with _POST_HOOKS_LOCK:
        if any(fn is existing for existing in _POST_HOOKS):
            logger.debug('钩子已注册（同一对象），跳过重复注册: %s',
                       _hook_name(fn))
            return
        _POST_HOOKS.append(fn)
        logger.info('已注册交付后钩子: %s', _hook_name(fn))
def _receipt_field(receipt: Any, name: str, default: Any = None) -> Any:
    if isinstance(receipt, dict):
        return receipt.get(name, default)
    return getattr(receipt, name, default)
def _explicit_receipt_dir(receipt: Any) -> str:
    for _attr in ('target_path', 'skill_dir', 'directory', 'root'):
        value = _path_text(_receipt_field(receipt, _attr))
        if value:
            return value
    return ''
def _resolve_delivery_target(receipt: Any) -> str:
    explicit = _explicit_receipt_dir(receipt)
    if explicit:
        return explicit
    paths = list(normalize_files_list(_receipt_field(receipt, 'files')))
    return common_parent_of(paths)
def _write_audit_safe(event: str, **payload: Any) -> None:
    try:
        write_audit(event, **payload)
    except Exception:
        logger.warning('审计事件写入失败（交付判定不受影响）: %s', event,
                       exc_info=True)
def _audit_delivery(result: dict[str, Any], duration_ms: float) -> None:
    event = 'delivery_blocked' if result['blocked'] else 'delivery_passed'
    count_key = 'failed' if result['blocked'] else 'passed'
    _write_audit_safe(event, total=result.get('total', 0),
                      duration_ms=round(duration_ms, 2),
                      **{count_key: result[count_key]})
def _delivery_hook(receipt: Any) -> dict[str, Any]:
    _t0 = time.monotonic()
    files = list(normalize_files_list(_receipt_field(receipt, 'files')))
    result = safe_delivery_check(target_path=_resolve_delivery_target(receipt),
                                 affected_files=files)
    _duration_ms = (time.monotonic() - _t0) * 1000
    blocked = result['blocked']
    _audit_delivery(result, _duration_ms)
    try:
        perf_trace('safe_ops_scan', round(_duration_ms, 2),
                   blocked=result.get('blocked', False))
    except Exception:
        logger.debug('perf_trace failed for safe_ops_scan', exc_info=True)
    if blocked:
        return {'safeops_blocked': True, 'details': result}
    logger.info('[SafeOps] 交付检查通过: %d/%d', result['passed'], result['total'])
    return {'safeops_blocked': False, 'passed': result['passed']}
def run_post_hooks(receipt: Any) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    with _POST_HOOKS_LOCK:
        hooks = tuple(_POST_HOOKS)
    for fn in hooks:
        hook = _hook_name(fn)
        try:
            out = fn(receipt)
            results.append({'hook': hook, 'ok': True, 'result': out})
        except Exception as exc:
            logger.warning('交付后钩子执行失败: %s: %s', hook, exc,
                         exc_info=True)
            results.append({'hook': hook, 'ok': False,
                            'error': f'{type(exc).__name__}: {exc}'})
    return results
def install(verbose: bool = True) -> dict[str, bool]:
    global _INSTALLED
    with _POST_HOOKS_LOCK:
        if not _INSTALLED:
            register_post_hook(_delivery_hook)
            _INSTALLED = True
    if verbose:
        logger.info('[SafeOps] 交付钩子已注册')
    return {'delivery': True}
def get_status() -> dict[str, Any]:
    guards = get_registered_guards()
    with _POST_HOOKS_LOCK:
        installed = _INSTALLED
        registered_hooks = [_hook_name(fn) for fn in _POST_HOOKS]
    return {
        'installed': installed,
        'registered_hooks': registered_hooks,
        'guards': len(guards),
        'guard_exec': get_guard_state(),
        'delivery_only_guards': list(_DELIVERY_ONLY_GUARDS),
        'unmapped_guards': sorted(
            set(guards) - set(_PREFLIGHT_GUARDS)
            - set(_POSTFLIGHT_GUARDS) - set(_DELIVERY_ONLY_GUARDS)),
        'hooks': {
            'preflight': '编码前: ' + '+'.join(_PREFLIGHT_GUARDS)
                         + ' (显式调用 safe_preflight)',
            'postflight': '编码后: ' + '+'.join(_POSTFLIGHT_GUARDS)
                          + ' (显式调用 safe_postflight)',
            'delivery': '交付前: 全量守卫 (含仅交付阶段 '
                        + '+'.join(_DELIVERY_ONLY_GUARDS)
                        + '; install() 注册 _delivery_hook, 审计留痕)',
        },
    }
_HISTORY_MAX_ENTRIES = 256
class SafeOpsOrchestrator:
    def __init__(self, auto_backup: bool = False) -> None:
        self.auto_backup = auto_backup
        self._history: list[dict] = []
    @staticmethod
    def _now_17() -> str:
        return str(time.time_ns() // 100)
    def _record_history(self, entry: dict) -> dict:
        stored = dict(entry)
        self._history.insert(0, stored)
        if len(self._history) > _HISTORY_MAX_ENTRIES:
            del self._history[_HISTORY_MAX_ENTRIES:]
        return dict(stored)
    def execute(self, operation: Any) -> dict:
        ts = self._now_17()
        entry = {"operation": str(operation), "timestamp": ts}
        if not self.auto_backup:
            status, backup_path = "ok", None
        elif isinstance(operation, dict):
            status, backup_path = self._backup_for(operation)
        else:
            logger.warning(
                "SafeOpsOrchestrator: 自动备份已开启但操作非 dict(%s)，"
                "无法定位备份目标，按 skipped 记录", type(operation).__name__)
            status, backup_path = "skipped", None
        entry["status"] = status
        entry["backup_path"] = backup_path
        return self._record_history(entry)
    @staticmethod
    def _backup_for(operation: dict) -> tuple[str, str | None]:
        raw_target = operation.get("target")
        target = _path_text(raw_target) if raw_target is not None else None
        if raw_target is not None and target is None:
            logger.warning(
                "SafeOpsOrchestrator: operation target 类型非法 %r，"
                "无法备份，按 backup_failed 处理", raw_target)
            return "backup_failed", None
        if not target:
            logger.warning(
                "SafeOpsOrchestrator: 自动备份已开启但 operation 缺少 target，"
                "无法定位备份目标，按 skipped 记录")
            return "skipped", None
        try:
            backup_path = file_backup(target)
        except (OSError, RuntimeError, ValueError):
            logger.warning("SafeOpsOrchestrator: 自动备份失败", exc_info=True)
            return "backup_failed", None
        if backup_path is None:
            logger.warning(
                "SafeOpsOrchestrator: 自动备份失败"
                "（文件级备份未产出备份路径）: target=%s", target)
            return "backup_failed", None
        return "ok", backup_path
    def history(self) -> list[dict]:
        return [dict(entry) for entry in self._history]
DEFAULT_MAX_FILE_OPERATIONS = 50
DEFAULT_EXECUTION_TIMEOUT_SEC = 120
DEFAULT_THROTTLE_DELAY_MS = 500
DEFAULT_MAX_DELETE_OPERATIONS = 10
_HISTORY_WINDOW_SEC = 300
_MAX_REPEAT_COUNT = 3
_SESSION_IDLE_ROLLOVER_SEC = DEFAULT_EXECUTION_TIMEOUT_SEC
_TRACE_DANGEROUS_OPS = frozenset({
    *_DELETE_OPS, *_MODIFY_OPS, OperationType.CLEANUP, OperationType.MERGE,
})
@dataclass(frozen=True)
class _SessionSnapshot:
    counter: int
    delete_count: int
    start_time: float
    last_op_time: float
class _SessionState:
    _lock = threading.Lock()
    _counters: ClassVar[dict[str, int]] = defaultdict(int)
    _start_time: ClassVar[dict[str, float]] = {}
    _delete_count: ClassVar[dict[str, int]] = defaultdict(int)
    _last_op_time: ClassVar[dict[str, float]] = {}
    _operation_history: ClassVar[dict[str, list]] = defaultdict(list)
    _PRUNE_INTERVAL: ClassVar[float] = 600.0
    _last_prune_ts: ClassVar[float] = 0.0
    @classmethod
    def get_session_id(cls, ctx: OperationContext) -> str:
        sid = ctx.metadata.get("session_id", "default")
        return sid if isinstance(sid, str) and sid else "default"
    @classmethod
    def _reset_locked(cls, session_id: str, now: float | None = None, *,
                      clear_history: bool = True) -> None:
        cls._counters[session_id] = 0
        cls._start_time[session_id] = time.time() if now is None else now
        cls._delete_count[session_id] = 0
        cls._last_op_time.pop(session_id, None)
        if not clear_history:
            return
        _prefix = _session_history_prefix(session_id)
        for _key in [k for k in cls._operation_history if k.startswith(_prefix)]:
            del cls._operation_history[_key]
    @classmethod
    def _task_window_expired_locked(cls, session_id: str, now: float) -> bool:
        last_activity = (cls._last_op_time.get(session_id, 0.0)
                         or cls._start_time.get(session_id, 0.0))
        return (last_activity > 0
                and now - last_activity >= _SESSION_IDLE_ROLLOVER_SEC)
    @classmethod
    def reset(cls, session_id: str) -> None:
        with cls._lock:
            cls._reset_locked(session_id)
    @classmethod
    def ensure_initialized(cls, session_id: str) -> None:
        with cls._lock:
            if session_id not in cls._start_time:
                cls._reset_locked(session_id)
    @classmethod
    def _increment_locked(cls, session_id: str, op_name: str,
                          now: float) -> int:
        cls._counters[session_id] += 1
        if op_name in _DELETE_OP_NAMES:
            cls._delete_count[session_id] += 1
        cls._last_op_time[session_id] = now
        return cls._counters[session_id]
    @classmethod
    def increment(cls, session_id: str, op_type: str) -> int:
        with cls._lock:
            return cls._increment_locked(session_id, op_type, time.time())
    @classmethod
    def _snapshot_locked(cls, session_id: str) -> _SessionSnapshot:
        return _SessionSnapshot(
            counter=cls._counters.get(session_id, 0),
            delete_count=cls._delete_count.get(session_id, 0),
            start_time=cls._start_time.get(session_id, 0.0),
            last_op_time=cls._last_op_time.get(session_id, 0),
        )
    @classmethod
    def acquire(cls, ctx: OperationContext,
                now: float) -> tuple[list[str], int]:
        session_id = cls.get_session_id(ctx)
        with cls._lock:
            if session_id not in cls._start_time:
                cls._reset_locked(session_id, now)
            elif cls._task_window_expired_locked(session_id, now):
                logger.info(
                    "[G15] 会话 %s 空闲超过 %ss，按新任务重置熔断预算",
                    session_id, _SESSION_IDLE_ROLLOVER_SEC)
                cls._reset_locked(session_id, now, clear_history=False)
            snapshot = cls._snapshot_locked(session_id)
            issues = _quota_issues(ctx, snapshot, now)
            if issues:
                return issues, snapshot.counter
            new_count = cls._increment_locked(
                session_id, _operation_name(ctx), now)
            return [], new_count
    @classmethod
    def snapshot(cls, session_id: str) -> _SessionSnapshot:
        with cls._lock:
            return cls._snapshot_locked(session_id)
    @classmethod
    def _prune_stale_history_locked(cls, now: float, window_sec: float) -> None:
        for key in [k for k, ts in cls._operation_history.items()
                    if not ts or now - max(ts) >= window_sec]:
            del cls._operation_history[key]
    @classmethod
    def record_operation(cls, op_key: str, now: float, window_sec: float) -> int:
        with cls._lock:
            if now - cls._last_prune_ts >= cls._PRUNE_INTERVAL:
                cls._last_prune_ts = now
                cls._prune_stale_history_locked(now, window_sec)
            fresh = [t for t in cls._operation_history.get(op_key, ())
                     if now - t < window_sec]
            fresh.append(now)
            cls._operation_history[op_key] = fresh
            return len(fresh)
def _quota_issues(ctx: OperationContext, snapshot: _SessionSnapshot,
                  now: float) -> list[str]:
    issues: list[str] = []
    if snapshot.counter >= DEFAULT_MAX_FILE_OPERATIONS:
        issues.append(
            f"操作次数已达上限: {snapshot.counter}/{DEFAULT_MAX_FILE_OPERATIONS}."
            f"操作被熔断.")
    if (_operation_name(ctx) in _DELETE_OP_NAMES
            and snapshot.delete_count >= DEFAULT_MAX_DELETE_OPERATIONS):
        issues.append(
            f"删除操作次数已达上限: "
            f"{snapshot.delete_count}/{DEFAULT_MAX_DELETE_OPERATIONS}."
            f"操作被熔断.")
    elapsed = now - snapshot.start_time
    if elapsed > DEFAULT_EXECUTION_TIMEOUT_SEC:
        issues.append(
            f"任务总耗时 {elapsed:.0f}s 超过超时限制 "
            f"{DEFAULT_EXECUTION_TIMEOUT_SEC}s.操作被熔断.")
    interval_ms = (now - snapshot.last_op_time) * 1000
    if snapshot.last_op_time > 0 and interval_ms < DEFAULT_THROTTLE_DELAY_MS:
        issues.append(
            f"操作间隔 {interval_ms:.0f}ms 低于最小间隔 "
            f"{DEFAULT_THROTTLE_DELAY_MS}ms.请降低操作频率.")
    return issues
def guard_throttle(ctx: OperationContext) -> GuardResult:
    if is_read_only_audit(ctx):
        return GuardResult(guard_name="G15", passed=True,
                           message="只读审计,跳过熔断计量（无真实操作）")
    if ctx.dry_run:
        return GuardResult(guard_name="G15", passed=True,
                           message="dry_run 演练,跳过熔断计量（无真实操作）")
    issues, new_count = _SessionState.acquire(ctx, time.time())
    if issues:
        return GuardResult(
            guard_name="G15", passed=False,
            level=GuardLevel.BLOCK,
            message=f"操作熔断: {len(issues)} 项超限",
            details=issues,
            fix_suggestion="拆分任务为多个子任务,或增加熔断阈值."
                           f"当前限制: {DEFAULT_MAX_FILE_OPERATIONS}次文件操作/任务, "
                           f"{DEFAULT_MAX_DELETE_OPERATIONS}次删除/任务, "
                           f"{DEFAULT_EXECUTION_TIMEOUT_SEC}s超时."
        )
    return GuardResult(guard_name="G15", passed=True,
                       message=f"操作计数: {new_count}/{DEFAULT_MAX_FILE_OPERATIONS}")
def _make_op_key(target: str, operation: str) -> str:
    raw = f"{_path_identity(target)}:{operation}"
    return hashlib.md5(raw.encode(), usedforsecurity=False).hexdigest()[:16]
def _session_history_prefix(session_id: str) -> str:
    return hashlib.md5(session_id.encode(),
                       usedforsecurity=False).hexdigest() + ":"
def _check_repeat_operation(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    if ctx.dry_run:
        return issues
    _target = target_path_str(ctx)
    op_key = _session_history_prefix(
        _SessionState.get_session_id(ctx)) + _make_op_key(
        _target, ctx.operation.value)
    now = time.time()
    repeat_count = _SessionState.record_operation(op_key, now, _HISTORY_WINDOW_SEC)
    if repeat_count >= _MAX_REPEAT_COUNT:
        issues.append(
            f"目标 {_target} 在 {_HISTORY_WINDOW_SEC}s 内被 "
            f"重复操作 {repeat_count} 次（{ctx.operation.value}）."
            f"已达重复上限 {repeat_count}/{_MAX_REPEAT_COUNT},可能存在重复执行风险."
        )
    elif repeat_count > 1:
        issues.append(
            f"目标 {_target} 在 {_HISTORY_WINDOW_SEC}s 内被 "
            f"重复操作 {repeat_count} 次（{ctx.operation.value}）."
            f"请确认是否需要重复执行."
        )
    return issues
def _check_idempotency_marker(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    if ctx.operation in _WRITE_SCOPE_OPS:
        idempotent = ctx.metadata.get("idempotent", None)
        if idempotent is None:
            issues.append(
                f"操作 {ctx.operation.value} 未声明幂等性."
                f"请在 metadata 中设置 idempotent=True/False."
            )
        elif not isinstance(idempotent, bool):
            issues.append(
                f"操作 {ctx.operation.value} 的幂等性声明类型非法"
                f"（{type(idempotent).__name__}）."
                f"idempotent 必须为 bool: True 或 False."
            )
    return issues
def _check_delete_already_gone(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    if (ctx.operation in _DELETE_OPS
            and isinstance(ctx.target_path, str) and ctx.target_path
            and not os.path.exists(ctx.target_path)):
        issues.append(
            f"删除目标 {ctx.target_path} 已经不存在."
            f"重复删除是无效操作,可能是 Agent 幻觉."
        )
    return issues
def guard_idempotency(ctx: OperationContext) -> GuardResult:
    issues: list[str] = []
    issues.extend(_check_repeat_operation(ctx))
    issues.extend(_check_idempotency_marker(ctx))
    issues.extend(_check_delete_already_gone(ctx))
    return issues_guard_result(
        "G22", "幂等性检查", "问题", issues,
        "确认操作是否需要重复执行."
        "在 metadata 中设置 idempotent=True 声明幂等性.",
        "幂等性检查通过",  # nosec B106 — 中文校验结论文案非密码
        level=GuardLevel.WARN)
def _check_scope_defined(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    if ctx.operation in _WRITE_SCOPE_OPS and not _defined_scope_files(ctx):
        issues.append(
            "操作范围未界定（affected_files 为空）."
            "无法评估影响范围,存在误操作风险."
        )
    return issues
def _check_intent_declared(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    expected = ctx.metadata.get("expected_outcome", "")
    if not (isinstance(expected, str) and expected.strip()):
        issues.append(
            "未声明预期结果（metadata.expected_outcome 为空）."
            "无法在操作后校验结果是否符合预期."
        )
    reason = ctx.metadata.get("reason", "")
    if not (isinstance(reason, str) and reason.strip()):
        issues.append(
            "未声明操作理由（metadata.reason 为空）."
            "无法判断操作是否必要."
        )
    return issues
def _check_target_ambiguity(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if is_read_only_audit(ctx):
        return issues
    target = target_path_str(ctx)
    if not target:
        return issues
    wildcard_text = (target[4:]
                     if os.name == "nt" and target.startswith("\\\\?\\")
                     else target)
    if '*' in wildcard_text or '?' in wildcard_text:
        issues.append(
            f"目标路径包含通配符: {target}."
            f"通配符可能匹配到意外的文件,建议明确指定目标."
        )
    if os.path.isdir(target) and ctx.operation in (
        OperationType.DELETE_FILE, OperationType.MODIFY_CODE,
    ):
        issues.append(
            f"目标 {target} 是目录,但操作类型是 {ctx.operation.value}."
            f"可能是目标识别错误."
        )
    if os.path.isfile(target) and ctx.operation == OperationType.DELETE_DIR:
        issues.append(
            f"目标 {target} 是文件,但操作类型是 DELETE_DIR."
            f"可能是目标识别错误."
        )
    return issues
def guard_intent_confirm(ctx: OperationContext) -> GuardResult:
    issues: list[str] = []
    issues.extend(_check_scope_defined(ctx))
    issues.extend(_check_intent_declared(ctx))
    issues.extend(_check_target_ambiguity(ctx))
    return issues_guard_result(
        "G19", "操作意图确认", "问题", issues,
        "明确操作目标、界定影响范围、声明预期结果和操作理由."
        "在 metadata 中设置 expected_outcome 和 reason.",
        "操作意图确认通过",  # nosec B106 — 中文校验结论文案非密码
        level=GuardLevel.WARN)
def _generate_diag_entry(ctx: OperationContext) -> dict:
    affected = list(normalize_files_list(ctx.affected_files))
    return {
        "timestamp": datetime.now().isoformat(),
        "operation": ctx.operation.value,
        "target_path": target_path_str(ctx),
        "affected_files": affected[:20],
        "dry_run": ctx.dry_run,
        "metadata_keys": list(ctx.metadata.keys()) if ctx.metadata else [],
        "file_count": len(affected),
    }
def _write_diag_log(entry: dict) -> None:
    if (not entry.get("target_path")
            and entry.get("file_count", 0) == 0
            and not entry.get("affected_files")):
        return
    _write_audit_safe("guard_diag_trail", **entry)
def _diag_target_issue(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if not target_path_str(ctx):
        issues.append("缺少 target_path,无法追溯操作目标")
    return issues
def _defined_scope_files(ctx: OperationContext) -> list[str]:
    files = list(normalize_files_list(ctx.affected_files))
    if files:
        return files
    target = target_path_str(ctx)
    if target and os.path.exists(target):
        return [target]
    return []
def _diag_scope_issue(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if not _defined_scope_files(ctx) and ctx.operation in _WRITE_SCOPE_OPS:
        issues.append("缺少 affected_files,无法追溯影响范围")
    return issues
def _diag_code_pair_issue(ctx: OperationContext) -> list[str]:
    issues: list[str] = []
    if ctx.operation in _MODIFY_OPS:
        before = ctx.metadata.get("before_code", "")
        after = ctx.metadata.get("after_code", "")
        if not _has_explicit_code_pair(before, after):
            issues.append(
                "代码修改操作缺少 before_code/after_code,"
                "无法生成 diff 用于诊断追溯"
            )
    return issues
def _check_diag_completeness(ctx: OperationContext) -> list[str]:
    if is_read_only_audit(ctx):
        return []
    issues: list[str] = []
    issues.extend(_diag_target_issue(ctx))
    issues.extend(_diag_scope_issue(ctx))
    issues.extend(_diag_code_pair_issue(ctx))
    return issues
def guard_diag_trail(ctx: OperationContext) -> GuardResult:
    entry = _generate_diag_entry(ctx)
    _write_diag_log(entry)
    if ctx.operation not in _TRACE_DANGEROUS_OPS:
        return GuardResult(guard_name="G18", passed=True,
                           message="诊断日志已记录")
    issues = _check_diag_completeness(ctx)
    if not issues:
        return GuardResult(guard_name="G18", passed=True,
                           message="诊断追踪完整,日志已记录")
    return GuardResult(
        guard_name="G18", passed=False, level=GuardLevel.WARN,
        message=f"诊断追踪不完整: {len(issues)} 项缺失",
        details=issues,
        fix_suggestion="补充 before_code/after_code 或 affected_files,"
                       "确保操作可追溯.")  # nosec B106 — 中文校验结论文案非密码
_BUILTIN_GUARDS: tuple[
    tuple[str, Callable[[OperationContext], GuardResult]], ...] = (
    ("G1", guard_backup),
    ("G2", guard_ast),
    ("G3", guard_syntax),
    ("G4", guard_imports),
    ("G5", guard_delete),
    ("G6", guard_funcbody),
    ("G7", guard_fstring),
    ("G8", guard_docstring),
    ("G9", guard_dictret),
    ("G10", guard_mro),
    ("G11", guard_slots),
    ("G12", guard_circular),
    ("G13", guard_default_deny),
    ("G14", guard_content_diag),
    ("G15", guard_throttle),
    ("G16", guard_path_sanitize),
    ("G17", guard_size_limit),
    ("G18", guard_diag_trail),
    ("G19", guard_intent_confirm),
    ("G20", guard_blast_radius),
    ("G21", guard_post_verify),
    ("G22", guard_idempotency),
    ("G23", guard_snapshot_diff),
    ("G24", guard_rollback),
    ("G25", guard_concurrent_state),
    ("G26", guard_safe_delete),
    ("G27", guard_recursion_depth),
    ("G28", guard_import_side_effect),
    ("G29", guard_atexit_register),
)
_PREPARE_STAGE_GUARDS: frozenset[str] = frozenset({"G1", "G15", "G24"})
def _register_builtin_guards() -> None:
    for name, guard_fn in _BUILTIN_GUARDS:
        register_guard(name, guard_fn,
                       stage=(_GUARD_STAGE_PREPARE
                              if name in _PREPARE_STAGE_GUARDS
                              else _GUARD_STAGE_CHECK))
_register_builtin_guards()

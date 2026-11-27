# ruff: noqa: I001
from __future__ import annotations
import ast
import difflib
import hashlib
import json
import logging
import os
import re
import shutil
import stat
import tempfile
import time
import zipfile
from collections.abc import Callable, Iterable, Iterator, Mapping
from dataclasses import dataclass, field
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Self
try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib
from jwsgj.build_preflight_guard import validate_skill
from jwsgj.diag_guard_io import (
    JSON_READ_DEGRADE_EXC,
    SKILL_DOC_FILENAME,
    normalize_out_path,
    safe_delete,
)
from jwsgj.diag_guard_io import (
    write_text_atomic as _write_text_atomic,
)
from jwsgj.diag_guard_state import (
    serialize_json,
)
from jwsgj.log_config import log_swallowed, safe_write_audit
from jwsgj.runtime_paths import (
    epoch_anchor_dir,
    incremental_snapshot_dir,
    lifecycle_state_dir,
    version_history_path,
)
from jwsgj.runtime_scope import (
    PACKAGE_EXCLUDE_DIR_NAMES,
    SCAN_IGNORE_DIRS_LOWER,
    STATE_DIR_NAME,
    is_package_excluded_file,
    is_pruned_scan_dir,
    is_scan_py_name,
    is_unregistered_package_root_file,
)
logger = logging.getLogger(__name__)
__all__ = [
    "VERSION_LINE_RE",
    "SkillEntry",
    "SkillSnapshotManager",
    "SkillVersionSnapshot",
    "VersionEntry",
    "bump_version",
    "clear_version_listeners",
    "compare_skill",
    "compute_current_snapshot",
    "compute_hash",
    "default_snapshot_dir",
    "detect_skill_changes",
    "execute_merge_plan",
    "extract_frontmatter_version",
    "frontmatter_span",
    "generate_monthly_report",
    "get_anchor_content",
    "get_skill_content",
    "get_version_history",
    "get_version_listener_count",
    "is_real_skills_root",
    "load_hash_snapshot",
    "notify_version_listeners",
    "package_skill",
    "partition_package_validation_errors",
    "read_skill_version",
    "read_skill_version_entry",
    "register_version_listener",
    "run_epoch",
    "save_anchor_snapshot",
    "save_hash_snapshot",
    "scan_py_files",
    "snapshot_skill",
    "unregister_version_listener",
    "update_anchors",
]
logger.info("build_skill_merge 已加载: %d 项导出", len(__all__))
_FRONTMATTER_LINE_START = r'(?:^|(?<=\r))'
_FRONTMATTER_LINE_END = (
    r'(?=[ \t]*(?:#[^\r\n]*)?(?:\r\n|\r|\n|\Z))'
)
VERSION_LINE_RE = re.compile(
    _FRONTMATTER_LINE_START
    + r'(version:[ \t]*)(?P<quote>["\']?)([^\s"\']+)(?P=quote)'
    + _FRONTMATTER_LINE_END,
    re.MULTILINE)
_NAME_LINE_RE = re.compile(
    _FRONTMATTER_LINE_START
    + r'name:[ \t]*(?P<quote>["\']?)(?P<value>[^\s"\']+)(?P=quote)'
    + _FRONTMATTER_LINE_END,
    re.MULTILINE)
_HISTORY_FILENAME = "_version_history.json"
_VALID_VERSION_RE = re.compile(r'^[0-9][0-9A-Za-z._+\-]*\Z')
def frontmatter_span(content: str) -> tuple[int, int] | None:
    lines = content.splitlines(keepends=True)
    if not lines:
        return None
    opening = lines[0].removeprefix("\ufeff").rstrip("\r\n")
    if opening[:1].isspace() or opening.rstrip(" \t") != "---":
        return None
    start = len(lines[0])
    pos = start
    for line in lines[1:]:
        if not line[:1].isspace() and line.rstrip() == "---":
            return (start, pos)
        pos += len(line)
    return None
def _version_match(content: str) -> re.Match[str] | None:
    span = frontmatter_span(content)
    return VERSION_LINE_RE.search(content, *span) if span else None
def extract_frontmatter_version(content: str) -> str | None:
    m = _version_match(content)
    return m.group(3) if m else None
def _extract_skill_name(content: str, skill_dir: str) -> str:
    span = frontmatter_span(content)
    m = _NAME_LINE_RE.search(content, *span) if span else None
    if m:
        return m.group("value")
    return os.path.basename(os.path.abspath(skill_dir))
def _is_valid_version(v: str) -> bool:
    if not isinstance(v, str):
        return False
    return bool(v) and len(v) <= 64 and bool(_VALID_VERSION_RE.match(v))
def _read_text_preserve_eol(path: str) -> tuple[str, str]:
    with open(path, encoding="utf-8", newline="") as fh:
        raw = fh.read()
    return raw, ("\r\n" if "\r\n" in raw else ("\r" if "\r" in raw else "\n"))
def _read_lf_normalized(path: str) -> tuple[str, str]:
    raw, eol = _read_text_preserve_eol(path)
    without_crlf = raw.replace("\r\n", "")
    styles = ("\r\n" in raw, "\n" in without_crlf, "\r" in without_crlf)
    if sum(styles) > 1:
        return raw, ""
    return raw.replace("\r\n", "\n").replace("\r", "\n"), eol
@dataclass
class VersionEntry:
    name: str
    current: str
    previous: str | None = None
    history: list[str] = field(default_factory=list)
_LISTENERS: dict[str, list[Callable[[str, str], Any]]] = {}
def register_version_listener(component: str, callback: Callable[[str, str], Any]) -> bool:
    if component not in _LISTENERS:
        _LISTENERS[component] = []
    if callback not in _LISTENERS[component]:
        _LISTENERS[component].append(callback)
        logger.debug("版本监听器已注册: %s", component)
        return True
    return False
def unregister_version_listener(component: str, callback: Callable[[str, str], Any]) -> bool:
    if component in _LISTENERS and callback in _LISTENERS[component]:
        _LISTENERS[component].remove(callback)
        return True
    return False
def get_version_listener_count(component: str | None = None) -> int:
    if component is not None:
        return len(_LISTENERS.get(component, []))
    return sum(len(v) for v in _LISTENERS.values())
def clear_version_listeners() -> None:
    _LISTENERS.clear()
def _collect_listener_callbacks(component: str) -> list[Callable[[str, str], Any]]:
    names: tuple[str, ...] = ("*",) if component == "*" else (component, "*")
    seen_ids: set[int] = set()
    callbacks: list[Callable[[str, str], Any]] = []
    for name in names:
        for cb in list(_LISTENERS.get(name, [])):
            if id(cb) in seen_ids:
                continue
            seen_ids.add(id(cb))
            callbacks.append(cb)
    return callbacks
def notify_version_listeners(component: str, old_version: str, new_version: str) -> int:
    callbacks = _collect_listener_callbacks(component)
    notified = 0
    for cb in callbacks:
        try:
            cb(old_version, new_version)
            notified += 1
        except Exception as exc:  # noqa: BLE001 — 第三方监听器异常必须隔离
            logger.warning("版本监听器 %s 通知失败(已隔离): %s",
                         getattr(cb, "__name__", repr(cb)), exc)
            safe_write_audit("version_listener_failed", component=component,
                             callback=getattr(cb, "__name__", repr(cb)),
                             error=str(exc))
    return notified
def _skill_md_path(skill_dir: str) -> Path:
    return Path(skill_dir) / SKILL_DOC_FILENAME
def _load_history_file(path: str) -> tuple[list[dict[str, Any]], bool]:
    if not os.path.isfile(path):
        return [], True
    try:
        with open(path, encoding="utf-8-sig") as fh:
            raw = fh.read()
    except FileNotFoundError as _swallow_e:
        log_swallowed(__name__, _swallow_e, context='_load_history_file:FileNotFoundError')
        return [], True
    except JSON_READ_DEGRADE_EXC as exc:
        logger.warning("_load_history_file: 读取失败 %s: %s", path, exc)
        return [], False
    if not raw.strip():
        return [], True
    try:
        data = json.loads(raw)
    except JSON_READ_DEGRADE_EXC as exc:
        logger.warning("_load_history_file: 解析失败 %s: %s", path, exc)
        return [], False
    if not isinstance(data, list):
        logger.warning("_load_history_file: 顶层非列表，拒绝覆盖 %s (%s)",
                       path, type(data).__name__)
        return [], False
    if not all(isinstance(item, dict) for item in data):
        logger.warning("_load_history_file: 列表含非对象条目，拒绝覆盖 %s", path)
        return [], False
    return data, True
def _invalid_skill_dir(skill_dir: Any, op: str) -> bool:
    if isinstance(skill_dir, (str, os.PathLike)):
        text = os.fspath(skill_dir)
        if not isinstance(text, str):
            logger.warning("%s: 非法 skill_dir 路径形态 %r，降级返回", op,
                           type(text).__name__)
            return True
        if not text.strip():
            logger.warning("%s: 空 skill_dir 无解析目标，降级返回", op)
            return True
        return False
    logger.warning("%s: 非法 skill_dir 类型 %r，降级返回", op,
                 type(skill_dir).__name__)
    return True
def read_skill_version(skill_dir: str) -> str | None:
    if _invalid_skill_dir(skill_dir, "read_skill_version"):
        return None
    current, _name = _read_skill_md_name_version(skill_dir)
    return current or None
def read_skill_version_entry(skill_dir: str) -> VersionEntry:
    if _invalid_skill_dir(skill_dir, "read_skill_version_entry"):
        return VersionEntry(name="", current="", previous=None, history=[])
    current, name = _read_skill_md_name_version(skill_dir)
    history_entries = get_version_history(skill_dir)
    valid_entries = [e for e in history_entries
                     if isinstance(e.get("new_version"), str) and e.get("new_version")]
    history = [e["new_version"] for e in valid_entries]
    last_old = valid_entries[-1].get("old_version") if valid_entries else None
    previous = last_old if isinstance(last_old, str) else None
    return VersionEntry(name=name, current=current,
                        previous=previous, history=history)
def _read_skill_md_name_version(skill_dir: str) -> tuple[str, str]:
    name = os.path.basename(os.path.abspath(skill_dir))
    try:
        with open(_skill_md_path(skill_dir), encoding="utf-8") as fh:
            content = fh.read()
        current = extract_frontmatter_version(content) or ""
        name = _extract_skill_name(content, skill_dir)
    except (OSError, UnicodeDecodeError, ValueError) as exc:
        logger.warning("读取 SKILL.md 失败，版本与名称使用默认值: %s", exc)
        return "", name
    return current, name
def get_version_history(skill_dir: str) -> list[dict[str, Any]]:
    if _invalid_skill_dir(skill_dir, "get_version_history"):
        return []
    try:
        path = version_history_path(skill_dir)
    except RuntimeError as exc:
        logger.warning("get_version_history: 历史路径解析被防线拦截，降级空: %s", exc)
        return []
    return _load_history_file(path)[0]
_HISTORY_MAX_ENTRIES = 500
def _append_history(history_path: str, entry: dict[str, Any]) -> bool:
    history, readable = _load_history_file(history_path)
    if not readable:
        logger.warning("_append_history: 历史文件损坏或结构非法，拒绝覆盖: %s",
                       history_path)
        safe_write_audit("version_history_append_refused", path=history_path)
        return False
    history.append(entry)
    if _HISTORY_MAX_ENTRIES == 0:
        history = []
    elif len(history) > _HISTORY_MAX_ENTRIES:
        history = history[-_HISTORY_MAX_ENTRIES:]
    try:
        _write_text_atomic(
            history_path, serialize_json(history, indent=2))
        return True
    except (OSError, TypeError, ValueError, RecursionError, MemoryError) as exc:
        logger.warning("_append_history: 落盘失败 %s: %s", history_path, exc)
        return False
_VERSION_CONST_RE = re.compile(
    r"(?m)(?:^|(?<=;))(?:\ufeff)?(?P<prefix>[ \t]*(?P<name>__version__|PACKAGE_VERSION)[ \t]*"
    r"(?::[ \t]*str[ \t]*)?=[ \t]*)(?P<quote>['\"])(?P<value>[^'\"\n]*)"
    r"(?P=quote)")
_VERSION_CONST_PRIORITY = ("PACKAGE_VERSION", "__version__")
_VERSION_FILE_NAME = "VERSION"
_PLAIN_VERSION_RE = re.compile(
    r"^[ \t]*(?:\ufeff)?(?P<value>[0-9][0-9A-Za-z._+\-]*)[ \t]*$")
_PYPROJECT_FILE_NAME = "pyproject.toml"
_PYPROJECT_VERSION_TABLES = (("project",), ("tool", "poetry"))
@dataclass(frozen=True)
class _VersionDeclaration:
    kind: str
    path: str
    symbol: str = ""
    def label(self) -> str:
        name = os.path.basename(self.path)
        if self.kind == "python-constant" and self.symbol:
            return f"{self.kind}:{self.symbol}@{name}"
        return f"{self.kind}:{name}"
def _root_py_files(skill_dir: str) -> list[str]:
    try:
        with os.scandir(skill_dir) as scanned:
            return [entry.path
                    for entry in sorted(scanned, key=lambda item: item.name)
                    if entry.is_file()
                    and entry.name.lower().endswith(".py")]
    except OSError as exc:
        logger.warning("_root_py_files: 列举 %s 失败: %s", skill_dir, exc)
        return []
def _module_version_declaration_lines(
        content: str) -> dict[tuple[int, int], tuple[str, str]]:
    try:
        tree = ast.parse(content.lstrip("\ufeff"))
    except (SyntaxError, ValueError):  # jwsgj:silent-ok 语法无效即无有效版本声明
        return {}
    declarations: dict[tuple[int, int], tuple[str, str]] = {}
    for node in tree.body:
        target = None
        value = None
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign):
            target, value = node.target, node.value
        if (isinstance(target, ast.Name)
                and target.id in _VERSION_CONST_PRIORITY
                and isinstance(value, ast.Constant)
                and isinstance(value.value, str)
                and _is_valid_version(value.value)):
            declarations[node.lineno, node.col_offset] = target.id, value.value
    return declarations
def _version_constant_matches(
        content: str) -> list[tuple[str, re.Match[str]]]:
    declarations = _module_version_declaration_lines(content)
    if not declarations:
        return []
    matches: list[tuple[str, re.Match[str]]] = []
    bom_text = content[:len(content) - len(content.lstrip("\ufeff"))]
    bom_byte_width = len(bom_text.encode("utf-8"))
    for match in _VERSION_CONST_RE.finditer(content):
        lineno = len(re.findall(r"\r\n?|\n", content[:match.start()])) + 1
        line_start = max(
            content.rfind("\n", 0, match.start()),
            content.rfind("\r", 0, match.start()),
        ) + 1
        column = len(content[line_start:match.start("name")].encode("utf-8"))
        if lineno == 1:
            column -= bom_byte_width
        symbol = match.group("name")
        if declarations.get((lineno, column)) == (symbol, match.group("value")):
            matches.append((symbol, match))
    return matches
def _version_constant_hits(
        content: str) -> list[tuple[str, re.Match[str]]]:
    matches = _version_constant_matches(content)
    return sorted(
        matches,
        key=lambda item: _VERSION_CONST_PRIORITY.index(item[0]),
    )
def _python_constant_declarations(skill_dir: str) -> list[_VersionDeclaration]:
    declarations: list[_VersionDeclaration] = []
    for path in _root_py_files(skill_dir):
        try:
            content, _eol = _read_lf_normalized(path)
        except (OSError, UnicodeDecodeError) as exc:
            logger.warning("版本声明扫描跳过不可读文件 %s: %s", path, exc)
            continue
        declarations.extend(
            _VersionDeclaration("python-constant", path, symbol)
            for symbol, _match in _version_constant_hits(content)
        )
    return declarations
def _toml_version_node(parsed: Any, table: tuple[str, ...]) -> Any:
    node = parsed
    for key in table:
        node = node.get(key) if isinstance(node, dict) else None
    return node
def _pyproject_declarations(skill_dir: str) -> list[_VersionDeclaration]:
    path = os.path.join(skill_dir, _PYPROJECT_FILE_NAME)
    if not os.path.isfile(path):
        return []
    try:
        with open(path, encoding="utf-8-sig") as fh:
            parsed = tomllib.loads(fh.read())
    except (OSError, UnicodeDecodeError, ValueError, RecursionError) as exc:
        logger.warning("pyproject 版本声明解析失败，跳过: %s (%s)", path, exc)
        return []
    declarations: list[_VersionDeclaration] = []
    for table in _PYPROJECT_VERSION_TABLES:
        node = _toml_version_node(parsed, table)
        version = node.get("version") if isinstance(node, dict) else None
        if isinstance(version, str) and _is_valid_version(version):
            declarations.append(_VersionDeclaration(
                "pyproject", path, ".".join(table)))
    return declarations
def _version_file_declarations(skill_dir: str) -> list[_VersionDeclaration]:
    path = os.path.join(skill_dir, _VERSION_FILE_NAME)
    if not os.path.isfile(path):
        return []
    try:
        with open(path, encoding="utf-8-sig") as fh:
            text = fh.read()
    except (OSError, UnicodeDecodeError) as exc:
        logger.warning("VERSION 文件读取失败，跳过: %s (%s)", path, exc)
        return []
    match = _PLAIN_VERSION_RE.match(text.strip())
    if match is None or not _is_valid_version(match.group("value")):
        return []
    return [_VersionDeclaration("version-file", path)]
def _discover_version_declarations(skill_dir: str) -> list[_VersionDeclaration]:
    declarations: list[_VersionDeclaration] = []
    for discover in (_python_constant_declarations,
                     _pyproject_declarations,
                     _version_file_declarations):
        declarations.extend(discover(skill_dir))
    return declarations
def _toml_key_pattern(key: str) -> str:
    escaped = re.escape(key)
    return rf"(?:{escaped}|\"{escaped}\"|'{escaped}')"
def _iter_toml_top_level_lines(
        content: str) -> Iterator[tuple[int, str, bool]]:
    """逐行产出 ``(行首偏移, 行文本, 是否位于 TOML 顶层)``。

    只有在字符串、注释、数组与内联表之外的行首 ``[`` 才可能是下一个表头；
    多行字符串或多行数组内部行首的 ``[`` 不能结束当前表区间。
    """
    state = "code"  # code | basic | literal | ml_basic | ml_literal
    depth = 0
    offset = 0
    for line in content.splitlines(keepends=True):
        top_level = state == "code" and depth == 0
        index = 0
        size = len(line)
        while index < size:
            char = line[index]
            if state == "code":
                if char == '"':
                    if line.startswith('"""', index):
                        state = "ml_basic"
                        index += 3
                        continue
                    state = "basic"
                elif char == "'":
                    if line.startswith("'''", index):
                        state = "ml_literal"
                        index += 3
                        continue
                    state = "literal"
                elif char == "#":
                    break
                elif char in "[{":
                    depth += 1
                elif char in "]}":
                    depth = max(depth - 1, 0)
            elif state == "basic":
                if char == "\\":
                    index += 2
                    continue
                if char == '"':
                    state = "code"
            elif state == "literal":
                if char == "'":
                    state = "code"
            elif state == "ml_basic":
                if char == "\\":
                    index += 2
                    continue
                if line.startswith('"""', index):
                    state = "code"
                    index += 3
                    continue
            elif state == "ml_literal" and line.startswith("'''", index):
                state = "code"
                index += 3
                continue
            index += 1
        yield offset, line, top_level
        offset += len(line)
def _pyproject_section_span(content: str,
                            table: tuple[str, ...]) -> tuple[int, int] | None:
    table_pattern = r"[ \t]*\.[ \t]*".join(
        _toml_key_pattern(part) for part in table)
    header_re = re.compile(
        rf"^[ \t]*(?:\ufeff)?\[[ \t]*{table_pattern}[ \t]*\][ \t]*"
        r"(?:#[^\r\n]*)?(?:\r\n|\r|\n|\Z)"
    )
    start = None
    for line_start, line, top_level in _iter_toml_top_level_lines(content):
        if start is None:
            if top_level and header_re.match(line):
                start = line_start + len(line)
        elif top_level and re.match(r"^[ \t]*\[", line):
            return start, line_start
    return (start, len(content)) if start is not None else None
@dataclass(frozen=True)
class _VersionWritePlan:
    path: str
    original: str
    updated: str
    eol: str
    changed: bool
def _toml_semantic_version(text: str, table: tuple[str, ...]) -> str | None:
    try:
        parsed = tomllib.loads(text.lstrip("\ufeff"))
    except (ValueError, RecursionError) as exc:
        logger.warning("pyproject 候选写点校验失败（TOML 不可解析）: %s", exc)
        return None
    node = _toml_version_node(parsed, table)
    version = node.get("version") if isinstance(node, dict) else None
    return version if isinstance(version, str) else None
_PYPROJECT_VERSION_BINDING_RE = re.compile(
    r"(?m)^(?P<prefix>[ \t]*(?:version|\"version\"|'version')"
    r"[ \t]*=[ \t]*)(?P<q>['\"])"
    r"(?P<value>[^'\"\n]*)(?P=q)")
def _plan_pyproject_version(path: str, table: tuple[str, ...],
                            new_version: str) -> _VersionWritePlan | None:
    try:
        content, eol = _read_lf_normalized(path)
    except (OSError, UnicodeDecodeError) as exc:
        logger.warning("pyproject 版本同步读取失败: %s (%s)", path, exc)
        return None
    span = _pyproject_section_span(content, table)
    if span is None:
        if _toml_semantic_version(content, table) == new_version:
            return _VersionWritePlan(path, content, content, eol, False)
        logger.warning("pyproject 未定位到版本表 %s，跳过同步: %s", table, path)
        return None
    section = content[span[0]:span[1]]
    for match in _PYPROJECT_VERSION_BINDING_RE.finditer(section):
        if match.group("value") == new_version:
            if _toml_semantic_version(content, table) == new_version:
                return _VersionWritePlan(path, content, content, eol, False)
            continue
        updated_section = (section[:match.start("value")] + new_version
                           + section[match.end("value"):])
        updated = content[:span[0]] + updated_section + content[span[1]:]
        if _toml_semantic_version(updated, table) == new_version:
            return _VersionWritePlan(path, content, updated, eol, True)
        logger.debug("pyproject 候选写点未改变语义版本，尝试下一个: %s",
                     match.group(0))
    if _toml_semantic_version(content, table) == new_version:
        return _VersionWritePlan(path, content, content, eol, False)
    logger.warning("pyproject 版本表内未找到可写 version 行，跳过同步: %s", path)
    return None
def _module_constant_has_version(content: str, symbol: str,
                                 version: str) -> bool:
    return any(name == symbol and value == version
               for name, value
               in _module_version_declaration_lines(content).values())
def _plan_constant_version(path: str, symbol: str,
                           new_version: str) -> _VersionWritePlan | None:
    try:
        content, eol = _read_lf_normalized(path)
    except (OSError, UnicodeDecodeError) as exc:
        logger.warning("版本常量同步读取失败: %s (%s)", path, exc)
        return None
    matches = [match for matched_symbol, match
               in _version_constant_matches(content)
               if matched_symbol == symbol]
    if not matches:
        logger.warning("版本常量同步未找到 %s 行，跳过: %s", symbol, path)
        return None
    for match in matches:
        if (match.group("value") == new_version
                and _module_constant_has_version(
                    content, symbol, new_version)):
            return _VersionWritePlan(path, content, content, eol, False)
        quote = match.group("quote")
        updated = (content[:match.start("prefix")] + match.group("prefix")
                   + quote + new_version + quote + content[match.end(0):])
        if _module_constant_has_version(updated, symbol, new_version):
            return _VersionWritePlan(path, content, updated, eol, True)
    logger.warning("版本常量候选写点未落到模块级声明，跳过: %s", path)
    return None
def _plan_version_file(path: str, new_version: str) -> _VersionWritePlan | None:
    try:
        content, eol = _read_lf_normalized(path)
    except (OSError, UnicodeDecodeError) as exc:
        logger.warning("VERSION 文件同步读取失败: %s (%s)", path, exc)
        return None
    match = _PLAIN_VERSION_RE.match(content.strip())
    if match is None:
        logger.warning("VERSION 文件内容不是单一版本号，跳过同步: %s", path)
        return None
    if match.group("value") == new_version:
        return _VersionWritePlan(path, content, content, eol, False)
    bom = "\ufeff" if content.startswith("\ufeff") else ""
    return _VersionWritePlan(path, content, bom + new_version + "\n", eol, True)
def _plan_version_declaration(declaration: _VersionDeclaration,
                              new_version: str) -> _VersionWritePlan | None:
    if declaration.kind == "python-constant":
        return _plan_constant_version(
            declaration.path, declaration.symbol, new_version)
    if declaration.kind == "pyproject":
        return _plan_pyproject_version(
            declaration.path, tuple(declaration.symbol.split(".")),
            new_version)
    if declaration.kind == "version-file":
        return _plan_version_file(declaration.path, new_version)
    logger.warning("未知版本声明形态，跳过同步: %s", declaration.kind)
    return None
def _apply_version_plan(plan: _VersionWritePlan) -> bool:
    if not plan.changed:
        return True
    try:
        _write_text_atomic(plan.path, plan.updated, newline=plan.eol)
        return True
    except OSError as exc:
        logger.warning("包版本声明写回失败: %s (%s)", plan.path, exc)
        return False
def _resolve_version_declarations(
        skill_dir: str, filename: str | None = None,
) -> tuple[list[_VersionDeclaration], str | None]:
    if filename:
        path = (filename if os.path.isabs(filename)
                else os.path.join(os.path.abspath(skill_dir), filename))
        if not os.path.isfile(path):
            return [], None
        try:
            content, _eol = _read_lf_normalized(path)
        except (OSError, UnicodeDecodeError) as exc:
            logger.warning("显式版本文件读取失败: %s (%s)", path, exc)
            return [], None
        hits = _version_constant_hits(content)
        if len(hits) > 1:
            symbols = sorted({symbol for symbol, _match in hits})
            message = ("显式版本文件存在多个版本常量声明: "
                       + ", ".join(symbols))
            logger.warning("显式文件内存在多个版本常量声明，拒绝自选写点: %s",
                           path)
            return [], message
        if not hits:
            logger.warning("显式文件内未找到版本常量声明，拒绝自选写点: %s",
                           path)
            return [], None
        return [_VersionDeclaration("python-constant", path, hits[0][0])], None
    declarations = _discover_version_declarations(skill_dir)
    paths = [os.path.normcase(os.path.abspath(item.path))
             for item in declarations]
    duplicated = sorted({path for path in paths if paths.count(path) > 1})
    if duplicated:
        logger.warning("同一文件存在多个版本声明，拒绝自选写点: %s",
                       [declaration.label() for declaration in declarations])
        return [], "同一文件存在多个版本声明: " + ", ".join(duplicated)
    return declarations, None
def _bump_fail(reason: str, message: str, data: Any = None) -> dict[str, Any]:
    safe_write_audit("version_bump_failed", reason=reason, message=message)
    return {"status": "error", "data": data, "message": message}
def _version_bump_result_data(
        skill_name: str, old_version: str, new_version: str, *,
        history_recorded: bool = False, package_synced: bool = False,
        version_source: str = "", version_sources: list[str] | None = None,
        notified: int = 0, **extra: Any) -> dict[str, Any]:
    sources = (list(version_sources) if version_sources is not None
               else ([version_source] if version_source else []))
    data = {
        "skill": skill_name,
        "old_version": old_version,
        "new_version": new_version,
        "history_recorded": history_recorded,
        "package_synced": package_synced,
        "version_source": version_source,
        "version_sources": sources,
        "notified": notified,
    }
    data.update(extra)
    return data
def bump_version(skill_dir: str, new_version: str, description: str = "",
                 dry_run: bool = False,
                 package_version_file: str | None = None) -> dict[str, Any]:
    if _invalid_skill_dir(skill_dir, "bump_version"):
        return _bump_fail(
            "invalid_skill_dir",
            f"非法技能目录: {skill_dir!r}（须为非空字符串或路径对象）")
    md_path = _skill_md_path(skill_dir)
    if not os.path.isfile(md_path):
        return _bump_fail("skill_md_missing", f"SKILL.md 不存在: {md_path}")
    history_path, err = _bump_history_path(skill_dir)
    if err is not None:
        return err
    content, eol, err = _bump_load_content(md_path)
    if err is not None:
        return err
    m, err = _bump_locate_version(content, new_version)
    if err is not None:
        return err
    old_version = m.group(3)
    skill_name = _extract_skill_name(content, skill_dir)
    declarations, conflict = _resolve_version_declarations(
        skill_dir, package_version_file)
    if conflict is not None:
        return _bump_fail(
            "package_version_ambiguous",
            f"包版本写点不唯一（{conflict}）；SKILL.md 未写盘",
            data=_version_bump_result_data(
                skill_name, old_version, new_version),
        )
    if package_version_file and not declarations:
        return _bump_fail(
            "package_version_declaration_missing",
            f"显式包版本文件不可同步: {package_version_file!r}；SKILL.md 未写盘",
            data=_version_bump_result_data(
                skill_name, old_version, new_version),
        )
    version_sources = [declaration.label() for declaration in declarations]
    version_source = version_sources[0] if version_sources else ""
    package_plans: list[_VersionWritePlan] = []
    for declaration in declarations:
        plan = _plan_version_declaration(declaration, new_version)
        if plan is None:
            return _bump_fail(
                "package_version_sync_failed",
                f"包版本声明不可同步: {declaration.label()}；SKILL.md 未写盘",
                data=_version_bump_result_data(
                    skill_name, old_version, new_version,
                    version_source=version_source,
                    version_sources=version_sources),
            )
        package_plans.append(plan)
    if dry_run:
        return {"status": "ok",
                "data": _version_bump_result_data(
                    skill_name, old_version, new_version,
                    version_source=version_source,
                    version_sources=version_sources, dry_run=True),
                "message": "dry_run 预览：未写盘、未通知"}
    err = _bump_write_version_line(md_path, m, new_version, content, eol)
    if err is not None:
        return err
    return _bump_commit(skill_dir, skill_name, old_version, new_version,
                        description, history_path, declarations, package_plans,
                        content, eol)
def _bump_history_path(skill_dir: str) -> tuple[str | None, dict | None]:
    try:
        return version_history_path(skill_dir), None
    except RuntimeError as exc:
        log_swallowed(__name__, exc, context='bump_version:RuntimeError')
        return None, _bump_fail(f"{STATE_DIR_NAME}_dir_invalid", str(exc))
def _bump_load_content(md_path: str) -> tuple[str | None, str, dict | None]:
    try:
        content, eol = _read_lf_normalized(md_path)
    except (OSError, UnicodeDecodeError) as exc:
        logger.warning("读取 SKILL.md 失败: %s", exc)
        return None, "\n", _bump_fail("skill_md_unreadable",
                                       f"读取 SKILL.md 失败: {exc}")
    return content, eol, None
def _bump_locate_version(content: str, new_version: str
                         ) -> tuple[re.Match[str] | None, dict | None]:
    m = _version_match(content)
    if not m:
        return None, _bump_fail("version_line_missing",
                                "SKILL.md frontmatter 中未找到 version: 行")
    if not _is_valid_version(new_version):
        return None, _bump_fail("invalid_version_format",
                                f"非法版本号格式: {new_version!r}（须以数字开头，"
                                f"仅含字母/数字/._+-，无空白与引号）")
    if m.group(3) == new_version:
        return None, _bump_fail("version_unchanged",
                                f"版本号未变化（{m.group(3)}），无需提升",
                                data={"old_version": m.group(3)})
    return m, None
def _bump_write_version_line(md_path: str, m: re.Match[str], new_version: str,
                             content: str, eol: str) -> dict | None:
    quote = m.group(2)
    new_line = m.group(1) + quote + new_version + quote
    updated = content[:m.start()] + new_line + content[m.end():]
    try:
        _write_text_atomic(md_path, updated, newline=eol)
    except OSError as exc:
        logger.warning("写回 SKILL.md 失败: %s", exc)
        return _bump_fail("skill_md_write_failed", f"写回 SKILL.md 失败: {exc}")
    return None
def _rollback_version_bump(
        skill_dir: str, applied: list[_VersionWritePlan],
        original_content: str, original_eol: str,
) -> list[str]:
    errors: list[str] = []
    try:
        _write_text_atomic(
            _skill_md_path(skill_dir), original_content, newline=original_eol)
    except OSError as exc:
        errors.append(f"SKILL.md 回滚失败: {exc}")
    for plan in applied:
        if not plan.changed:
            continue
        try:
            _write_text_atomic(plan.path, plan.original, newline=plan.eol)
        except OSError as exc:
            errors.append(f"包版本声明回滚失败: {plan.path}: {exc}")
    return errors
def _bump_commit(skill_dir: str, skill_name: str, old_version: str,
                 new_version: str, description: str, history_path: str,
                 declarations: list[_VersionDeclaration],
                 package_plans: list[_VersionWritePlan],
                 original_content: str, original_eol: str,
                 ) -> dict[str, Any]:
    version_sources = [declaration.label() for declaration in declarations]
    version_source = version_sources[0] if version_sources else ""
    failure_data = _version_bump_result_data(
        skill_name, old_version, new_version,
        version_source=version_source, version_sources=version_sources)
    applied: list[_VersionWritePlan] = []
    for plan in package_plans:
        if not _apply_version_plan(plan):
            rollback_errors = _rollback_version_bump(
                skill_dir, applied, original_content, original_eol)
            failure_data["rollback_completed"] = not rollback_errors
            failure_data["rollback_errors"] = rollback_errors
            return _bump_fail(
                "package_version_write_failed",
                f"包版本声明写回失败: {plan.path}；"
                + ("版本提升已撤销" if not rollback_errors else
                   f"回滚不完整: {rollback_errors}"),
                data=failure_data,
            )
        applied.append(plan)
    package_synced = bool(package_plans)
    entry = {
        "skill": skill_name,
        "old_version": old_version,
        "new_version": new_version,
        "description": description or "",
        "timestamp": datetime.now(UTC).isoformat(timespec="seconds"),
    }
    if not _append_history(history_path, entry):
        rollback_errors = _rollback_version_bump(
            skill_dir, applied, original_content, original_eol)
        failure_data["rollback_completed"] = not rollback_errors
        failure_data["rollback_errors"] = rollback_errors
        return _bump_fail(
            "history_write_failed",
            "版本历史落盘失败，版本提升及包版本同步已撤销"
            if not rollback_errors else
            f"版本历史落盘失败且回滚不完整: {rollback_errors}",
            data=failure_data,
        )
    notified = notify_version_listeners(skill_name, old_version, new_version)
    safe_write_audit("version_bumped", skill=skill_name,
                     old_version=old_version, new_version=new_version,
                     description=description or "",
                     history_recorded=True,
                     package_synced=package_synced,
                     version_source=version_source, notified=notified)
    return {"status": "ok",
            "data": _version_bump_result_data(
                skill_name, old_version, new_version,
                history_recorded=True, package_synced=package_synced,
                version_source=version_source,
                version_sources=version_sources, notified=notified),
            "message": f"版本已提升 {old_version} -> {new_version}"}
_PACKAGE_DIR = Path(__file__).resolve().parent
_SKILLS_BASE = Path(__file__).resolve().parent.parent
def _sha256_of_file(filepath: str) -> str:
    digest = hashlib.sha256()
    with open(filepath, "rb") as f:
        while chunk := f.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()
_HASH_SNAPSHOT_FILENAME = "_hash_snapshot.json"
_SHORT_HASH_HEX_LEN = 16
_SHORT_HASH_RE = re.compile(rf"[0-9a-f]{{{_SHORT_HASH_HEX_LEN}}}")
_ARCHIVED_SKILLS_DIRNAME = "_archived_skills"
_SNAPSHOT_PRUNE_DIRS_LOWER = (SCAN_IGNORE_DIRS_LOWER
                              | {_ARCHIVED_SKILLS_DIRNAME})
def _hash_file_short(filepath: str) -> str:
    try:
        return _sha256_of_file(filepath)[:_SHORT_HASH_HEX_LEN]
    except OSError as e:
        logger.warning("[Incremental] 文件哈希失败，快照中止 %s: %s", filepath, e)
        raise
def scan_py_files(skill_dir: str, *, strict: bool = False) -> list[str]:
    py_files: list[str] = []
    def _on_walk_error(exc: OSError) -> None:
        logger.warning("[Incremental] 目录遍历失败: %s", exc)
        if strict:
            raise exc
    for root, dirs, filenames in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = [
            d for d in dirs
            if not is_pruned_scan_dir(d, _SNAPSHOT_PRUNE_DIRS_LOWER)
        ]
        py_files.extend(
            os.path.join(root, f) for f in filenames if is_scan_py_name(f))
    py_files.sort()
    return py_files
def compute_current_snapshot(skill_dir: str) -> dict[str, str]:
    snapshot: dict[str, str] = {}
    for fp in scan_py_files(skill_dir, strict=True):
        rel = os.path.relpath(fp, skill_dir).replace("\\", "/")
        snapshot[rel] = _hash_file_short(fp)
    return snapshot
def default_snapshot_dir(project_root: str) -> str:
    root_abs = os.path.abspath(project_root)
    name = os.path.basename(os.path.normpath(root_abs)) or "_unnamed_project"
    bucket = "".join(
        ch for ch in name if ch not in '\\/:*?"<>|' and ord(ch) >= 32
    ) or "_unnamed_project"
    fingerprint = hashlib.md5(
        os.path.normcase(root_abs).replace(os.sep, "/").encode("utf-8"),
        usedforsecurity=False,
    ).hexdigest()[:8]
    return os.path.join(
        incremental_snapshot_dir(root_abs), f"{bucket}_{fingerprint}",
    )
def save_hash_snapshot(snapshot: dict[str, str], report_dir: str) -> str:
    path = os.path.join(report_dir, _HASH_SNAPSHOT_FILENAME)
    payload = json.dumps(snapshot, ensure_ascii=False, indent=2, default=str)
    _write_text_atomic(path, payload)
    logger.info("[Incremental] 哈希快照已保存: %d 个文件", len(snapshot))
    return path
def _is_valid_snapshot_entry(rel: Any, digest: Any) -> bool:
    if (not isinstance(rel, str) or not isinstance(digest, str)
            or _SHORT_HASH_RE.fullmatch(digest) is None):
        return False
    if (not rel or "\\" in rel or os.path.isabs(rel)
            or re.match(r"^[A-Za-z]:", rel)):
        return False
    parts = rel.split("/")
    return (rel.lower().endswith(".py")
            and all(part not in ("", ".", "..") for part in parts))
def load_hash_snapshot(report_dir: str) -> dict[str, str] | None:
    path = os.path.join(report_dir, _HASH_SNAPSHOT_FILENAME)
    if not os.path.exists(path):
        return None
    try:
        with open(path, encoding="utf-8-sig") as f:
            data = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError, OSError,
            RecursionError) as e:
        logger.warning("[Incremental] 哈希快照损坏，回退全量模式: %s", e)
        return None
    if not isinstance(data, dict):
        logger.warning("[Incremental] 哈希快照类型无效（非 dict），回退全量模式")
        return None
    if not all(_is_valid_snapshot_entry(rel, digest)
               for rel, digest in data.items()):
        logger.warning("[Incremental] 哈希快照条目无效（路径或哈希），回退全量模式")
        return None
    return data
def _safe_child_dir(root: Path, name: object) -> Path | None:
    if isinstance(name, os.PathLike):
        try:
            name = os.fspath(name)
        except TypeError:  # jwsgj:silent-ok 路径对象不可 fspath 转换，按无安全子目录返回 None
            return None
    if not isinstance(name, str) or not name or name in ('.', '..'):
        return None
    if any(ch in name for ch in (':', '/', '\\', '\x00')):
        return None
    if Path(name).name != name:
        return None
    return root / name
def _dir_nonempty(path: Path) -> bool | None:
    try:
        if not stat.S_ISDIR(path.stat().st_mode):
            return False
        return any(path.iterdir())
    except (FileNotFoundError, NotADirectoryError):
        return False
    except OSError as exc:
        logger.warning('枚举 %s 失败，完整度无法判定: %s', path, exc)
        return None
def _skill_completeness_score(skill_dir: Path) -> int | None:
    score = 0
    for sub in ('scripts', 'tests'):
        nonempty = _dir_nonempty(skill_dir / sub)
        if nonempty is None:
            return None
        score += nonempty
    return score
def _merge_root_error(reason: str, skills_root: object) -> dict:
    logger.warning('execute_merge_plan skills_root 不可用: %r（%s），拒绝执行',
                 skills_root, reason)
    return {
        'status': 'error',
        'executed': False,
        'archived': [],
        'skipped': [],
        'errors': [{'entry': None,
                    'reason': '技能根目录' + reason + ': '
                              + repr(skills_root)[:200]}],
        'archive_root': None,
    }
def _resolve_merge_root(skills_root: object) -> tuple[str | None, dict | None]:
    root_text = normalize_out_path(skills_root)
    if root_text is None:
        return None, _merge_root_error('参数非法或空白', skills_root)
    if not os.path.isdir(root_text):
        return None, _merge_root_error('不存在或不是目录', skills_root)
    return root_text, None
def _merge_entry_semantic_rejection(entry) -> tuple[str, dict] | None:
    if not isinstance(entry, dict):
        return ('errors', {'entry': str(entry)[:200],
                           'reason': '计划项非对象形态，跳过'})
    action = entry.get('action')
    if action != 'MERGE':
        return ('skipped', {'entry': entry,
                            'reason': f'非 MERGE 动作({action!r})需 AI 执行功能整合，'
                                      '不自动归档'})
    skill_a, skill_b = entry.get('skill_a'), entry.get('skill_b')
    if isinstance(skill_a, str) and skill_a == skill_b:
        return ('errors', {'entry': entry,
                           'reason': f'同名技能对，无可归并差异: {skill_a!r}'})
    return None
def _same_physical_dir(left: Path, right: Path) -> bool | None:
    samefile = getattr(os.path, 'samefile', None)
    if samefile is None:
        logger.warning('当前平台不支持 samefile，无法确认归档目录物理身份')
        return None
    try:
        return samefile(left, right)
    except OSError as exc:
        log_swallowed(__name__, exc, context='_same_physical_dir:OSError')
        return None
def _resolve_merge_entry_dirs(entry, root: Path) -> tuple[dict, tuple[str, dict] | None]:
    names = [entry.get('skill_a'), entry.get('skill_b')]
    dirs = {}
    invalid_names: list[str] = []
    for skill_name in names:
        child = _safe_child_dir(root, skill_name)
        if child is None:
            invalid_names.append(str(skill_name))
        else:
            dirs[skill_name] = child
    missing_names = [n for n, d in dirs.items() if not d.is_dir()]
    if invalid_names or missing_names or len(dirs) < 2:
        return {}, ('errors', {'entry': entry,
                               'reason': '技能名非法或目录不存在: '
                                         + str(invalid_names + missing_names)})
    try:
        root_real = root.resolve(strict=True)
        resolved_dirs = [dirs[name].resolve(strict=True) for name in names]
    except (OSError, RuntimeError) as exc:
        return {}, ('errors', {
            'entry': entry,
            'reason': f'技能目录真实路径解析失败，归档失败关闭: {exc}',
        })
    if any(resolved == root_real or not resolved.is_relative_to(root_real)
           for resolved in resolved_dirs):
        return {}, ('errors', {
            'entry': entry,
            'reason': '技能目录真实路径越出技能根或指向技能根本身，归档失败关闭: '
                      + ' / '.join(map(str, resolved_dirs)),
        })
    same_physical = _same_physical_dir(dirs[names[0]], dirs[names[1]])
    if same_physical is not False:
        reason = ('技能名互为别名指向同一物理目录: ' if same_physical
                  else '无法确认技能目录物理身份，归档失败关闭: ')
        return {}, ('errors', {
            'entry': entry,
            'reason': reason + f'{names[0]!r} / {names[1]!r}'})
    return dirs, None
def _follow_merge_redirect(name: object, redirects: dict[str, str]) -> object:
    seen: set[str] = set()
    while isinstance(name, str) and name in redirects and name not in seen:
        seen.add(name)
        name = redirects[name]
    return name
def _register_merge_entry(entry, root: Path, archive_root: Path,
                          execute: bool, result: dict,
                          redirects: dict[str, str]) -> None:
    rejection = _merge_entry_semantic_rejection(entry)
    if rejection is not None:
        channel, reject_item = rejection
        result[channel].append(reject_item)
        return
    resolved_entry = dict(entry)
    for key in ('skill_a', 'skill_b'):
        resolved_entry[key] = _follow_merge_redirect(entry.get(key), redirects)
    if (isinstance(resolved_entry['skill_a'], str)
            and resolved_entry['skill_a'] == resolved_entry['skill_b']):
        result['skipped'].append({
            'entry': entry,
            'reason': '技能已在同一归并组收敛，跳过重复计划项',
        })
        return
    dirs, dir_rejection = _resolve_merge_entry_dirs(resolved_entry, root)
    if dir_rejection is not None:
        result['errors'].append(dir_rejection[1])
        return
    a_dir = dirs[resolved_entry['skill_a']]
    b_dir = dirs[resolved_entry['skill_b']]
    score_a, score_b = _skill_completeness_score(a_dir), _skill_completeness_score(b_dir)
    if score_a is None or score_b is None:
        result['errors'].append({
            'entry': entry,
            'reason': '技能完整度目录不可读，无法确认保留方，归档失败关闭',
        })
        return
    keep_dir, archive_dir = (a_dir, b_dir) if score_a >= score_b else (b_dir, a_dir)
    item = {'keep': keep_dir.name, 'archive': archive_dir.name,
            'overlap': entry.get('overlap')}
    if not execute:
        result['archived'].append(item)
        redirects[archive_dir.name] = keep_dir.name
        return
    archived_before = len(result['archived'])
    _archive_entry_dirs(entry, keep_dir, archive_dir, archive_root, result)
    if len(result['archived']) > archived_before:
        redirects[archive_dir.name] = keep_dir.name
def _archive_entry_dirs(entry, keep_dir: Path, archive_dir: Path,
                        archive_root: Path, result: dict) -> None:
    dest = archive_root / archive_dir.name
    if dest.exists():
        result['errors'].append({'entry': entry,
                                 'reason': '归档目标已存在，跳过: ' + str(dest)})
        logger.error("技能归档目标已存在: %s", dest)
        return
    try:
        archive_root.mkdir(parents=True, exist_ok=True)
        shutil.move(str(archive_dir), str(dest))
        result['archived'].append({
            'keep': keep_dir.name,
            'archive': archive_dir.name,
            'overlap': entry.get('overlap'),
        })
        logger.info("技能归档: %s → %s (保留: %s, overlap: %s)",
                  archive_dir.name, archive_root, keep_dir.name,
                  entry.get('overlap'))
    except OSError as exc:
        result['errors'].append(
            {'entry': entry, 'reason': '归档失败: ' + str(exc)})
        logger.exception("技能归档失败: %s → %s", archive_dir.name, archive_root)
def _normalize_execute_flag(value: object) -> bool:
    if value is True:
        return True
    if value is not False and value is not None:
        logger.warning('execute_merge_plan execute 非布尔值: %r，按预览处理',
                     value)
    return False
def execute_merge_plan(merge_plan: list[dict], skills_root: str,
                       execute: bool = False) -> dict:
    root_text, rejected = _resolve_merge_root(skills_root)
    if rejected is not None:
        return rejected
    execute = _normalize_execute_flag(execute)
    root = Path(root_text)
    archive_root = (root / _ARCHIVED_SKILLS_DIRNAME
                    / datetime.now().strftime('%Y%m%d_%H%M%S_%f'))
    result: dict = {
        'status': 'ok',
        'executed': bool(execute),
        'archived': [],
        'skipped': [],
        'errors': [],
        'archive_root': str(archive_root) if execute else None,
    }
    if merge_plan is not None and not isinstance(merge_plan, (list, tuple)):
        logger.warning('execute_merge_plan merge_plan 非列表形态: %r，拒绝执行',
                     merge_plan)
        result.update(status='error', executed=False, archive_root=None)
        result['errors'].append({
            'entry': None,
            'reason': 'merge_plan 必须是列表、元组或 None，拒绝把非法计划当作成功空计划',
        })
        return result
    redirects: dict[str, str] = {}
    for entry in merge_plan or []:
        _register_merge_entry(
            entry, root, archive_root, execute, result, redirects)
    result['status'] = 'error' if result['errors'] else 'ok'
    logger.info("execute_merge_plan 完成: execute=%s, 归档 %d, 跳过 %d, 错误 %d",
              execute, len(result['archived']), len(result['skipped']),
              len(result['errors']))
    return result
def _sequence_payload(payload: Any, label: str, *,
                      wrap_scalar: bool) -> list[Any]:
    if payload is None:
        return []
    if isinstance(payload, (str, bytes)):
        if wrap_scalar:
            return [payload]
        logger.warning("[Version] %s 接收标量载荷（按空序列处理，需传可迭代容器）: %s",
                     label, type(payload).__name__)
        return []
    if isinstance(payload, Mapping) or not isinstance(payload, Iterable):
        logger.warning("[Version] %s 接收非法序列载荷（降级空）: %s",
                     label, type(payload).__name__)
        return []
    return list(payload)
_STATUS_CHANGED = "CHANGED"
_STATUS_UNCHANGED = "UNCHANGED"
_STATUS_NEW = "NEW"
_STATUS_MISSING = "MISSING_CURRENT"
def compute_hash(content: str) -> str:
    if not isinstance(content, str):
        logger.warning("[Epoch] compute_hash 非文本入参(%s)，按不可计算返回空串",
                       type(content).__name__)
        return ""
    return hashlib.sha256(content.encode("utf-8")).hexdigest()
def _read_text_safe(path: Path) -> str | None:
    if not path.is_file():
        return None
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return None
    except (OSError, UnicodeDecodeError) as e:
        logger.warning("[Epoch] 文件读取失败，降级跳过: %s (%s)", path, e)
    return None
def _anchor_text(value: Any) -> str:
    if value is None:
        return ""
    try:
        return os.fsdecode(os.fspath(value)).strip()
    except TypeError:
        logger.debug("路径入参不支持 fsdecode，回落 str(): %r", value, exc_info=True)
        return str(value).strip()
def _skills_base_path(skills_base: str | os.PathLike | None) -> Path:
    raw = _anchor_text(skills_base)
    return Path(raw) if raw else _SKILLS_BASE
def _invalid_skill_name(skill_name: Any, op: str) -> bool:
    if isinstance(skill_name, (str, os.PathLike)):
        return False
    logger.warning("[Epoch] %s 忽略非法技能名: %r", op, skill_name)
    return True
def _resolve_skill_location(skill_name: Any, skills_base: str | None,
                            op: str) -> tuple[Path, tuple[str, ...]] | None:
    if _invalid_skill_name(skill_name, op):
        return None
    raw = _anchor_text(skill_name)
    if not raw:
        logger.warning("[Epoch] %s 忽略空白技能名", op)
        return None
    try:
        base_real = _skills_base_path(skills_base).resolve()
        candidate = Path(raw)
        if not candidate.is_absolute():
            candidate = base_real / candidate
        target = candidate.resolve()
        rel = target.relative_to(base_real)
    except (OSError, ValueError, RuntimeError, TypeError) as exc:
        logger.warning("[Epoch] %s 拒绝越界或非法技能名 %r: %s", op, skill_name, exc)
        return None
    if not rel.parts:
        logger.warning("[Epoch] %s 拒绝技能根本身: %r", op, skill_name)
        return None
    if any(part in ("", "..") for part in rel.parts):
        logger.warning("[Epoch] %s 拒绝非规范技能路径: %r", op, skill_name)
        return None
    return base_real, rel.parts
def get_skill_content(skill_name: str, skills_base: str | None = None) -> str | None:
    located = _resolve_skill_location(skill_name, skills_base, "get_skill_content")
    if located is None:
        return None
    base, parts = located
    return _read_text_safe(base.joinpath(*parts) / SKILL_DOC_FILENAME)
def _anchor_dir_for(skills_base: str | os.PathLike | None) -> Path:
    base = os.path.realpath(str(_skills_base_path(skills_base)))
    key = hashlib.md5(base.encode("utf-8"), usedforsecurity=False).hexdigest()[:10]
    return Path(epoch_anchor_dir(base)) / key
def is_real_skills_root(candidate: str | os.PathLike | None,
                        skills_base: str | os.PathLike | None = None) -> bool:
    raw = _anchor_text(candidate)
    if not raw:
        return True
    try:
        cand = Path(os.path.realpath(os.path.abspath(raw)))
        real_root = Path(os.path.realpath(str(_skills_base_path(skills_base))))
        return cand == real_root or real_root in cand.parents
    except (OSError, ValueError) as _e:
        log_swallowed(__name__, _e, context='is_real_skills_root:OSError')
        return False
def get_anchor_content(skill_name: str, skills_base: str | None = None) -> str | None:
    located = _resolve_skill_location(skill_name, skills_base, "get_anchor_content")
    if located is None:
        return None
    _base, parts = located
    anchor_md = (_anchor_dir_for(skills_base).joinpath(*parts)
                 / SKILL_DOC_FILENAME)
    return _read_text_safe(anchor_md)
def save_anchor_snapshot(skill_name: str, content: str,
                         skills_base: str | None = None) -> bool:
    if _invalid_skill_name(skill_name, "save_anchor_snapshot"):
        return False
    if not isinstance(content, str):
        logger.warning("[Epoch] save_anchor_snapshot 拒收非文本内容(%s): %r",
                       type(content).__name__, skill_name)
        return False
    located = _resolve_skill_location(skill_name, skills_base, "save_anchor_snapshot")
    if located is None:
        return False
    _base, parts = located
    try:
        anchor_skill_dir = _anchor_dir_for(skills_base).joinpath(*parts)
        anchor_md = anchor_skill_dir / SKILL_DOC_FILENAME
        _write_text_atomic(str(anchor_md), content)
        return True
    except OSError as e:
        logger.warning("[Epoch] 锚点快照写失败，跳过 %s: %s", skill_name, e)
        return False
def compare_skill(skill_name: str, skills_base: str | None = None) -> dict[str, Any]:
    current = get_skill_content(skill_name, skills_base)
    anchor = get_anchor_content(skill_name, skills_base)
    if current is None:
        return {"skill": skill_name, "status": _STATUS_MISSING}
    current_hash = compute_hash(current)
    if anchor is None:
        return {
            "skill": skill_name,
            "status": _STATUS_NEW,
            "current_hash": current_hash,
        }
    anchor_hash = compute_hash(anchor)
    if current_hash == anchor_hash:
        return {
            "skill": skill_name,
            "status": _STATUS_UNCHANGED,
            "hash": current_hash,
        }
    diff = list(difflib.unified_diff(
        anchor.splitlines(keepends=True),
        current.splitlines(keepends=True),
        fromfile=f"{skill_name}/SKILL.md (anchor)",
        tofile=f"{skill_name}/SKILL.md (current)",
    ))
    return {
        "skill": skill_name,
        "status": _STATUS_CHANGED,
        "current_hash": current_hash,
        "anchor_hash": anchor_hash,
        "diff": "".join(diff),
    }
def _normalize_skills_root(skills_root: Any) -> str | None:
    if skills_root is None:
        return str(_SKILLS_BASE)
    if not isinstance(skills_root, (str, os.PathLike)):
        logger.warning("[Epoch] run_epoch() 收到非法 skills_root 类型 %r，降级空报告",
                     type(skills_root).__name__)
        return None
    return str(_skills_base_path(skills_root))
def _bucket_comparisons(comparisons: list[Any]) -> tuple[
        dict[str, list[dict[str, Any]]], list[dict[str, Any]], list[Any]]:
    buckets: dict[str, list[dict[str, Any]]] = {
        _STATUS_CHANGED: [], _STATUS_NEW: [],
        _STATUS_UNCHANGED: [], _STATUS_MISSING: [],
    }
    valid: list[dict[str, Any]] = []
    invalid: list[Any] = []
    for comp in comparisons:
        if not isinstance(comp, dict):
            invalid.append(comp)
            continue
        status = comp.get("status")
        bucket = buckets.get(status) if isinstance(status, str) else None
        if bucket is None:
            invalid.append(comp)
            continue
        valid.append(comp)
        bucket.append(comp)
    return buckets, valid, invalid
def generate_monthly_report(
        comparisons: Iterable[dict[str, Any]] | None,
        consistency_issues: Iterable[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    consistency_issues = _sequence_payload(
        consistency_issues, "generate_monthly_report consistency_issues",
        wrap_scalar=False)
    comparisons = _sequence_payload(
        comparisons, "generate_monthly_report comparisons",
        wrap_scalar=False)
    buckets, valid, invalid_entries = _bucket_comparisons(comparisons)
    if invalid_entries:
        logger.warning("[Epoch] generate_monthly_report 跳过非 dict 或未知状态对比条目: %r",
                     invalid_entries[:3])
    month_str = datetime.now(UTC).strftime("%Y-%m")
    changed = buckets[_STATUS_CHANGED]
    new_skills = buckets[_STATUS_NEW]
    unchanged = buckets[_STATUS_UNCHANGED]
    missing = buckets[_STATUS_MISSING]
    report = {
        "type": "epoch_knowledge",
        "timestamp": time.time(),
        "month": month_str,
        "summary": {
            "total_skills": len(valid),
            "changed": len(changed),
            "new": len(new_skills),
            "unchanged": len(unchanged),
            "missing_current": len(missing),
            "consistency_issues": len(consistency_issues),
        },
        "changed_details": changed,
        "new_skills": new_skills,
        "missing_details": missing,
        "consistency_issues": consistency_issues,
    }
    logger.info("[Epoch] 月度知识报告已生成（纯内存）: month=%s changed=%d new=%d",
              month_str, len(changed), len(new_skills))
    return report
def _refresh_anchor_entry(comp: Any, skills_base: str | None) -> str | None:
    if not isinstance(comp, dict):
        logger.warning("[Epoch] update_anchors 跳过非 dict 对比条目: %r", comp)
        return None
    skill_name = comp.get("skill")
    if not isinstance(skill_name, (str, os.PathLike)) or not skill_name:
        logger.warning("[Epoch] update_anchors 跳过缺/非法 skill 键的对比条目: %r", comp)
        return None
    if comp.get("status") not in (_STATUS_CHANGED, _STATUS_NEW):
        return None
    content = get_skill_content(skill_name, skills_base)
    if content is not None and save_anchor_snapshot(skill_name, content, skills_base):
        return _anchor_text(skill_name)
    return None
def update_anchors(comparisons: Iterable[dict[str, Any]] | None,
                   skills_base: str | None = None) -> list[str]:
    comparisons = _sequence_payload(comparisons, "update_anchors comparisons",
                                    wrap_scalar=False)
    updated: list[str] = []
    for comp in comparisons:
        skill_name = _refresh_anchor_entry(comp, skills_base)
        if skill_name is not None:
            updated.append(skill_name)
    logger.info("[Epoch] 锚点已更新: %d 个技能", len(updated))
    safe_write_audit("anchors_updated", skills=updated, count=len(updated))
    return updated
def _is_skill_dir(item: Path) -> bool:
    try:
        return item.is_dir() and (item / SKILL_DOC_FILENAME).is_file()
    except OSError as e:
        logger.debug("[Epoch] 条目探测失败（跳过）: %s (%s)", item, e)
        return False
def _discover_skills(skills_root: str) -> list[str]:
    root = Path(skills_root)
    try:
        if not root.exists():
            return []
        items = list(root.iterdir())
    except OSError as e:
        logger.warning("[Epoch] 技能根目录枚举失败（返回空）: %s (%s)", root, e)
        return []
    return sorted(item.name for item in items if _is_skill_dir(item))
def _normalize_skill_names(names: Any) -> list[str]:
    payload = _sequence_payload(names, "run_epoch() 技能名", wrap_scalar=True)
    valid: list[str] = []
    invalid: list[Any] = []
    for item in payload:
        name = (_anchor_text(item).strip()
                if isinstance(item, (str, os.PathLike)) else "")
        if name:
            valid.append(name)
        else:
            invalid.append(item)
    if invalid:
        logger.warning("[Epoch] run_epoch() 跳过非法技能名条目: %r", invalid[:3])
    return valid
def run_epoch(skills_root: str | os.PathLike | None = None,
              skill_dirs: list[str | os.PathLike] | None = None) -> dict[str, Any]:
    base = _normalize_skills_root(skills_root)
    if base is None:
        return generate_monthly_report([], [])
    names = (skill_dirs if skill_dirs is not None
             else _discover_skills(base))
    names = _normalize_skill_names(names)
    logger.info("[Epoch] === evolve_knowledge: %d 个技能 ===", len(names))
    comparisons = []
    for skill_name in names:
        result = compare_skill(skill_name, skills_base=base)
        comparisons.append(result)
        logger.info("[Epoch]   %s: %s", skill_name, result["status"])
    report = generate_monthly_report(comparisons, [])
    update_anchors(comparisons, skills_base=base)
    return report
def _nz(value: Any, default: Any) -> Any:
    return default if value is None else value
def _duplicate_skill_names(*skill_groups: list[dict]) -> set[str]:
    duplicates: set[str] = set()
    for skills in skill_groups:
        counts: dict[str, int] = {}
        for item in skills:
            name = item.get("name") if isinstance(item, Mapping) else None
            if isinstance(name, str) and name:
                counts[name] = counts.get(name, 0) + 1
        duplicates.update(name for name, count in counts.items() if count > 1)
    return duplicates
def _skill_hash_map(skills: list[dict], duplicate_names: set[str]) -> dict[str, str]:
    result: dict[str, str] = {}
    for item in skills:
        if not isinstance(item, Mapping):
            continue
        name, file_hash = item.get("name"), item.get("hash")
        if not (isinstance(name, str) and name
                and isinstance(file_hash, str) and file_hash):
            continue
        key = name
        if name in duplicate_names:
            path = item.get("path")
            if isinstance(path, str) and path.strip():
                key = os.path.normcase(os.path.normpath(path))
            else:
                logger.warning(
                    "[Snapshot] 同名技能缺少有效 path，变化比对退化为名称键: %s",
                    name)
        result[key] = file_hash
    return result
def _diff_hash_maps(baseline: dict[str, str],
                    current: dict[str, str]) -> tuple[list[str], list[str], list[str]]:
    added = sorted(current.keys() - baseline.keys())
    removed = sorted(baseline.keys() - current.keys())
    modified = sorted(name for name in baseline.keys() & current.keys()
                      if baseline[name] != current[name])
    return added, removed, modified
def _path_covered_by_scan_failure(path: str,
                                   failed_paths: set[str]) -> bool:
    candidate = os.path.normcase(os.path.abspath(path))
    for failed in failed_paths:
        try:
            if os.path.commonpath((candidate, failed)) == failed:
                return True
        except (OSError, ValueError):
            continue
    return False
def _failure_blocked_keys(skills: list[dict], duplicate_names: set[str],
                          failed_paths: set[str]) -> set[str]:
    blocked: set[str] = set()
    for item in skills:
        if not isinstance(item, Mapping):
            continue
        name, path = item.get("name"), item.get("path")
        if not (isinstance(name, str) and name
                and isinstance(path, str) and path.strip()):
            continue
        key = os.path.normcase(os.path.normpath(path))
        if _path_covered_by_scan_failure(key, failed_paths):
            blocked.add(key if name in duplicate_names else name)
    return blocked
def _exclude_scan_failure_keys(
        changes: list[str], skills: list[dict], duplicate_names: set[str],
        scan_failures: list[str], channel: str,
) -> list[str]:
    if not scan_failures or not changes:
        return changes
    failed_paths = {os.path.normcase(os.path.abspath(item))
                    for item in scan_failures}
    blocked = _failure_blocked_keys(skills, duplicate_names, failed_paths)
    origin = "基线" if channel == "added" else "当前"
    if not blocked:
        logger.warning(
            "[Snapshot] %s扫描失败且无法归因到具体技能，本轮不产出 %s 结论: %s",
            origin, channel, scan_failures[:3])
        return []
    kept = [key for key in changes if key not in blocked]
    if len(kept) != len(changes):
        logger.warning(
            "[Snapshot] %s扫描失败，已从 %s 中排除 %d 个不确定条目: %s",
            origin, channel, len(changes) - len(kept), sorted(blocked)[:3])
    return kept
@dataclass
class SkillEntry:
    name: str
    path: str
    hash: str
    version: str = ""
    size: int = 0
    loaded_at: str = ""
    manifest_valid: bool = False
    def to_dict(self: Self) -> dict[str, Any]:
        return {
            "name": self.name, "path": self.path,
            "hash": self.hash, "version": self.version, "size": self.size,
            "loaded_at": self.loaded_at, "manifest_valid": self.manifest_valid,
        }
    @classmethod
    def from_dict(cls: type[Self], data: dict) -> Self:
        return cls(
            name=_nz(data.get("name"), ""), path=_nz(data.get("path"), ""),
            hash=_nz(data.get("hash"), ""),
            version=_nz(data.get("version"), ""), size=_nz(data.get("size"), 0),
            loaded_at=_nz(data.get("loaded_at"), ""),
            manifest_valid=_nz(data.get("manifest_valid"), False),
        )
@dataclass
class SkillVersionSnapshot:
    session_id: str
    created_at: str
    skills: list[dict] = field(default_factory=list)
    skill_count: int = 0
    total_size: int = 0
    scan_failures: list[str] = field(default_factory=list)
    def to_dict(self: Self) -> dict[str, Any]:
        return {
            "session_id": self.session_id, "created_at": self.created_at,
            "skills": self.skills, "skill_count": self.skill_count,
            "total_size": self.total_size,
            "partial": bool(self.scan_failures),
            "scan_failures": list(self.scan_failures),
        }
    @classmethod
    def from_dict(cls: type[Self], data: dict) -> Self:
        skills_raw = data.get("skills") or []
        if not isinstance(skills_raw, list):
            skills_raw = []
        failures_raw = data.get("scan_failures") or []
        if not isinstance(failures_raw, list):
            failures_raw = []
        return cls(
            session_id=_nz(data.get("session_id"), ""),
            created_at=_nz(data.get("created_at"), ""),
            skills=[s for s in skills_raw if isinstance(s, dict)],
            skill_count=_nz(data.get("skill_count"), 0),
            total_size=_nz(data.get("total_size"), 0),
            scan_failures=[item for item in failures_raw
                           if isinstance(item, str) and item],
        )
class SkillSnapshotManager:
    _SNAPSHOT_FILE_NAME = "skill_version_snapshot.json"
    def __init__(self: Self, state_dir: str | None = None) -> None:
        raw = None if state_dir is None else normalize_out_path(state_dir)
        if raw is None:
            if state_dir is not None:
                logger.warning(
                    "[Snapshot] state_dir 非法或空白（%r），回退默认状态目录",
                    state_dir)
            raw = str(Path(lifecycle_state_dir(str(_PACKAGE_DIR))))
        self.state_dir = Path(raw)
        self.snapshot_file = self.state_dir / self._SNAPSHOT_FILE_NAME
        self._scan_failures: list[str] = []
    def _record_scan_failure(self: Self, path: Path) -> None:
        self._scan_failures.append(
            os.path.normcase(os.path.abspath(os.fspath(path))))
    @staticmethod
    def _parse_md_version(md_path: Path) -> str:
        try:
            text = md_path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            logger.debug("读取 frontmatter 失败，降级空串跳过: %s: %s", md_path, exc)
            return ""
        return extract_frontmatter_version(text) or ""
    def scan_skill_dirs(self: Self, skill_dirs: list[str]) -> list[SkillEntry]:
        entries: list[SkillEntry] = []
        self._scan_failures = []
        for skill_dir in _sequence_payload(
                skill_dirs, "scan_skill_dirs 目录", wrap_scalar=True):
            try:
                raw_skill_dir = os.fspath(skill_dir)
            except TypeError:
                logger.warning("[Snapshot] 跳过非法技能目录条目: %r", skill_dir)
                continue
            if not isinstance(raw_skill_dir, str) or not raw_skill_dir.strip():
                logger.warning("[Snapshot] 跳过空白或非法技能目录条目: %r", skill_dir)
                continue
            path = Path(raw_skill_dir)
            single = self._scan_one_skill(path)
            if single is not None:
                entries.append(single)
                continue
            entries.extend(self._scan_root(path))
        return entries
    def _scan_root(self: Self, path: Path) -> list[SkillEntry]:
        try:
            items = list(path.iterdir())
        except FileNotFoundError as e:
            logger.warning("[Snapshot] 技能目录不存在，记录为扫描失败: %s (%s)", path, e)
            self._record_scan_failure(path)
            return []
        except OSError as e:
            logger.warning("[Snapshot] 目录枚举失败（跳过）: %s (%s)", path, e)
            self._record_scan_failure(path)
            return []
        found: list[SkillEntry] = []
        for item in sorted(items, key=lambda entry: entry.name.lower()):
            if not self._is_dir_entry(item):
                continue
            entry = self._scan_one_skill(item)
            if entry is not None:
                found.append(entry)
        return found
    def _is_dir_entry(self: Self, item: Path) -> bool:
        try:
            return item.is_dir()
        except OSError as e:
            logger.warning("[Snapshot] 条目类型探测失败，记录为扫描失败: %s (%s)", item, e)
            self._record_scan_failure(item)
            return False
    def _scan_one_skill(self: Self, item: Path) -> SkillEntry | None:
        item = Path(os.path.abspath(os.fspath(item)))
        md_path = item / SKILL_DOC_FILENAME
        manifest_path = item / ".manifest.json"
        try:
            has_skill_doc = md_path.is_file()
            manifest_valid = has_skill_doc and manifest_path.is_file()
        except OSError as e:
            logger.warning("[Snapshot] 条目类型探测失败，记录为扫描失败: %s (%s)",
                           item, e)
            self._record_scan_failure(item)
            return None
        if not has_skill_doc:
            return None
        total_size = self._dir_total_size(item)
        try:
            md_hash = _sha256_of_file(str(md_path))
        except (OSError, ValueError) as e:
            logger.warning("[Snapshot] 跳过哈希失败的技能目录: %s (%s)", item, e)
            self._record_scan_failure(item)
            return None
        return SkillEntry(
            name=item.name,
            path=str(item),
            hash=md_hash,
            version=self._parse_md_version(md_path),
            size=total_size,
            loaded_at=datetime.now(UTC).isoformat(),
            manifest_valid=manifest_valid,
        )
    @staticmethod
    def _dir_total_size(item: Path) -> int:
        total_size = 0
        try:
            for entry in item.rglob("*"):
                try:
                    if entry.is_file():
                        total_size += entry.stat().st_size
                except OSError as e:
                    logger.debug("文件状态探测失败（跳过）: %s", e)
        except OSError as e:
            logger.debug("[Snapshot] 目录遍历中断（体积按已累计计）: %s (%s)", item, e)
        return total_size
    def create_snapshot(self: Self, skill_dirs: list[str],
                        session_id: str = "") -> SkillVersionSnapshot:
        entries = self.scan_skill_dirs(skill_dirs)
        if self._scan_failures:
            logger.warning("[Snapshot] %d 个技能扫描失败，本次快照为部分结果: %s",
                           len(self._scan_failures),
                           self._scan_failures[:3])
        snapshot = SkillVersionSnapshot(
            session_id=session_id or datetime.now(UTC).isoformat(),
            created_at=datetime.now(UTC).isoformat(),
            skills=[e.to_dict() for e in entries],
            skill_count=len(entries),
            total_size=sum(e.size for e in entries),
            scan_failures=sorted(set(self._scan_failures)),
        )
        self._persist_snapshot(snapshot)
        return snapshot
    def _persist_snapshot(self: Self, snapshot: SkillVersionSnapshot) -> None:
        persisted = snapshot
        if snapshot.scan_failures:
            previous = self.load_snapshot()
            if previous is not None:
                failed_paths = {
                    os.path.normcase(os.path.abspath(item))
                    for item in snapshot.scan_failures
                }
                current_paths = {
                    normalized
                    for item in snapshot.skills
                    if (normalized := _normalized_skill_path(item.get("path")))
                    is not None
                }
                carried = [
                    item for item in previous.skills
                    if (normalized := _normalized_skill_path(item.get("path")))
                    is not None
                    and normalized not in current_paths
                    and _path_covered_by_scan_failure(normalized, failed_paths)
                ]
                if carried:
                    skills = [*snapshot.skills, *carried]
                    carried_size = sum(
                        item.get("size", 0) for item in carried
                        if isinstance(item.get("size"), int)
                        and not isinstance(item.get("size"), bool)
                    )
                    persisted = SkillVersionSnapshot(
                        session_id=snapshot.session_id,
                        created_at=snapshot.created_at,
                        skills=skills,
                        skill_count=len(skills),
                        total_size=snapshot.total_size + carried_size,
                        scan_failures=list(snapshot.scan_failures),
                    )
                    logger.info(
                        "[Snapshot] 部分扫描落盘保留上一份基线的 %d 个失败区域条目",
                        len(carried),
                    )
        snap_path = str(self.snapshot_file)
        audit_fields = {
            "skill_count": len(persisted.skills),
            "total_size": persisted.total_size,
            "session_id": persisted.session_id,
            "partial": bool(persisted.scan_failures),
            "scan_failure_count": len(persisted.scan_failures),
        }
        try:
            _write_text_atomic(
                snap_path,
                json.dumps(persisted.to_dict(), ensure_ascii=False,
                           indent=2, default=str))
        except (OSError, TypeError, ValueError) as exc:
            logger.warning("[Snapshot] 快照落盘失败（内存快照仍返回）: %s (%s)",
                         snap_path, exc)
            safe_write_audit("snapshot_created", persisted=False,
                             error=str(exc), **audit_fields)
            return
        logger.info("[Snapshot] 技能快照已保存: %s 个技能", len(persisted.skills))
        safe_write_audit("snapshot_created", persisted=True, **audit_fields)
    def load_snapshot(self: Self) -> SkillVersionSnapshot | None:
        snapshot_file = self.snapshot_file
        if not snapshot_file.is_file():
            return None
        try:
            data = json.loads(snapshot_file.read_text(encoding="utf-8-sig"))
        except FileNotFoundError:
            return None
        except (OSError, ValueError, RecursionError) as e:
            logger.warning("[Snapshot] 快照加载失败: %s", e)
            return None
        if not isinstance(data, dict):
            logger.warning("[Snapshot] 快照顶层非 JSON 对象（%s），视为损坏",
                         type(data).__name__)
            return None
        skills = data.get("skills", [])
        scan_failures = data.get("scan_failures", [])
        if (not isinstance(skills, list)
                or not all(isinstance(item, dict) for item in skills)):
            logger.warning("[Snapshot] 快照 skills 容器或条目非法，视为损坏")
            return None
        if (not isinstance(scan_failures, list)
                or not all(isinstance(item, str) and item
                           for item in scan_failures)):
            logger.warning("[Snapshot] 快照 scan_failures 容器或条目非法，视为损坏")
            return None
        return SkillVersionSnapshot.from_dict(data)
    def detect_changes(self: Self, skill_dirs: list[str]) -> dict[str, Any]:
        last = self.load_snapshot()
        current_skills = [e.to_dict() for e in self.scan_skill_dirs(skill_dirs)]
        scan_failures = sorted(set(self._scan_failures))
        if last is None:
            duplicate_names = _duplicate_skill_names(current_skills)
            current_map = _skill_hash_map(current_skills, duplicate_names)
            return {"added": sorted(current_map), "modified": [],
                    "removed": [], "scan_failures": scan_failures}
        duplicate_names = _duplicate_skill_names(last.skills, current_skills)
        current_map = _skill_hash_map(current_skills, duplicate_names)
        added, removed, modified = _diff_hash_maps(
            _skill_hash_map(last.skills, duplicate_names), current_map)
        added = _exclude_scan_failure_keys(
            added, current_skills, duplicate_names, last.scan_failures, "added")
        removed = _exclude_scan_failure_keys(
            removed, last.skills, duplicate_names, scan_failures, "removed")
        if added or modified or removed or scan_failures:
            safe_write_audit("skill_changes_detected",
                             added=added, modified=modified, removed=removed,
                             scan_failures=scan_failures,
                             baseline_scan_failures=last.scan_failures,
                             added_count=len(added), modified_count=len(modified),
                             removed_count=len(removed))
        return {"added": added, "modified": modified, "removed": removed,
                "scan_failures": scan_failures}
    def restore(self: Self, version: str, skill_dir: str = "") -> dict[str, Any]:
        snap = self.load_snapshot()
        if snap is None:
            return {"status": "error", "data": None,
                    "message": "无可用快照，无法恢复", "version": version}
        if skill_dir is not None and not isinstance(skill_dir, (str, os.PathLike)):
            return {
                "status": "error", "data": None, "version": version,
                "message": f"非法 skill_dir 类型: {type(skill_dir).__name__}",
            }
        matches = _select_snapshot_skills(
            snap.skills, _normalized_skill_path(skill_dir), version)
        return {
            "status": "ok",
            "version": version,
            "session_id": snap.session_id,
            "skill_count": len(matches),
            "skills": matches,
            "message": "快照仅记录元数据；文件内容回滚需结合外部版本备份",
        }
def _normalized_skill_path(value: Any) -> str | None:
    if not isinstance(value, (str, os.PathLike)):
        return None
    path = os.fspath(value)
    if not isinstance(path, str) or not path.strip():
        return None
    return os.path.normcase(os.path.abspath(path))
def _select_snapshot_skills(skills: list[dict], target: str | None,
                            version: str) -> list[dict]:
    matches = ([s for s in skills
                if _normalized_skill_path(s.get("path")) == target]
               if target is not None else skills)
    if version and matches:
        matches = [s for s in matches if s.get("version") == version]
    return matches
def _snapshot_manager_for(skill_dir: str) -> SkillSnapshotManager | None:
    try:
        state_dir = default_snapshot_dir(skill_dir)
    except RuntimeError as exc:
        log_swallowed(__name__, exc,
                      context='_snapshot_manager_for:RuntimeError')
        return None
    return SkillSnapshotManager(state_dir=state_dir)
def snapshot_skill(skill_dir: str, label: str = "", memo: str = "") -> dict[str, Any]:
    label = "" if label is None else str(label)
    memo = "" if memo is None else str(memo)
    if _invalid_skill_dir(skill_dir, "snapshot_skill"):
        return {"status": "error", "message": "非法技能目录，未生成快照",
                "skill_dir": "", "label": label, "memo": memo,
                "skills": [], "skill_count": 0, "total_size": 0,
                "session_id": "", "created_at": ""}
    manager = _snapshot_manager_for(skill_dir)
    if manager is None:
        return {"status": "error", "message": "状态目录不可用，未生成快照",
                "skill_dir": os.fsdecode(os.fspath(skill_dir)),
                "label": label, "memo": memo, "skills": [],
                "skill_count": 0, "total_size": 0, "session_id": "",
                "created_at": ""}
    snap = manager.create_snapshot([skill_dir], session_id=label)
    result = snap.to_dict()
    result["skill_dir"] = os.fsdecode(os.fspath(skill_dir))
    result["label"] = label
    result["memo"] = memo
    return result
def detect_skill_changes(skill_dir: str,
                         since_version: str | None = None) -> dict[str, Any]:
    if _invalid_skill_dir(skill_dir, "detect_skill_changes"):
        return {"status": "error", "message": "非法技能目录，未执行变化检测",
                "added": [], "modified": [], "removed": [],
                "scan_failures": []}
    manager = _snapshot_manager_for(skill_dir)
    if manager is None:
        return {"status": "error", "message": "状态目录不可用，未执行变化检测",
                "added": [], "modified": [], "removed": [],
                "scan_failures": []}
    changes = manager.detect_changes([skill_dir])
    if since_version:
        changes["since_version"] = since_version
    return changes
_BYTES_PER_KB = 1024.0
def _coerce_path_arg(value: object, label: str) -> str | None:
    normalized = normalize_out_path(value)
    if normalized is None:
        logger.error("[SkillAdapter] 打包校验失败: 非法%s %r", label, value)
    return normalized
def _coerce_skill_packaging_dir(skill_dir: str) -> str | None:
    raw = _coerce_path_arg(skill_dir, "技能目录")
    return None if raw is None else os.path.abspath(raw)
def _coerce_packaging_output_dir(output_dir: str | None, skill_dir: str) -> str | None:
    if output_dir is None:
        return os.path.dirname(skill_dir)
    return _coerce_path_arg(output_dir, "输出目录")
def _kept_package_dir(dirname: str) -> bool:
    return not is_pruned_scan_dir(dirname, PACKAGE_EXCLUDE_DIR_NAMES)
def _package_arcname(skill_dir: str, file_path: str) -> str:
    return os.path.relpath(file_path, os.path.dirname(skill_dir)).replace(os.sep, "/")
def _iter_packaged_entries(skill_dir: str, walk_errors: list[str] | None = None):
    def _on_walk_error(exc: OSError) -> None:
        if walk_errors is not None:
            walk_errors.append(str(exc))
        logger.warning("[SkillAdapter] 打包遍历失败: %s", exc)
    root_norm = os.path.normpath(skill_dir)
    for root, dirs, files in os.walk(skill_dir, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if _kept_package_dir(d)]
        at_root = os.path.normpath(root) == root_norm
        for file in files:
            if file.lower().endswith(".skill") or is_package_excluded_file(file):
                continue
            if at_root and is_unregistered_package_root_file(file):
                continue
            file_path = os.path.join(root, file)
            yield file_path, _package_arcname(skill_dir, file_path)
def _resolve_package_output(output_dir: str | None, skill_dir: str) -> str | None:
    resolved = _coerce_packaging_output_dir(output_dir, skill_dir)
    if resolved is None:
        return None
    if resolved.lower().endswith(".skill") and not os.path.isdir(resolved):
        return os.path.abspath(resolved)
    if os.path.exists(resolved) and not os.path.isdir(resolved):
        logger.error("[SkillAdapter] 输出目录已是同名文件，拒绝拼包: %s", resolved)
        return None
    return os.path.abspath(
        os.path.join(resolved, f"{os.path.basename(skill_dir)}.skill"))
def _write_archive_member(zf: zipfile.ZipFile, file_path: str,
                          arcname: str) -> None:
    if (arcname != SKILL_DOC_FILENAME
            and not arcname.endswith("/" + SKILL_DOC_FILENAME)):
        zf.write(file_path, arcname)
        return
    try:
        with open(file_path, "rb") as _fh:
            raw = _fh.read()
    except OSError as exc:
        log_swallowed(__name__, exc, context="_write_archive_member:OSError")
        zf.write(file_path, arcname)
        return
    zf.writestr(arcname, raw.replace(b"\r\n", b"\n").replace(b"\r", b"\n"))
def _write_skill_archive(skill_dir: str, output_path: str) -> None:
    fd, temp_path = tempfile.mkstemp(
        prefix=f".{os.path.basename(output_path)}.", suffix=".skill",
        dir=os.path.dirname(output_path))
    os.close(fd)
    walk_errors: list[str] = []
    try:
        with zipfile.ZipFile(temp_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for file_path, arcname in _iter_packaged_entries(skill_dir, walk_errors):
                _write_archive_member(zf, file_path, arcname)
        if walk_errors:
            raise OSError(
                "打包遍历失败，归档不完整，已放弃交付: "
                + "; ".join(walk_errors[:3]))
        size_kb = os.path.getsize(temp_path) / _BYTES_PER_KB
        os.replace(temp_path, output_path)
        logger.info("[OK] 打包完成: %s (%.1f KB)", output_path, size_kb)
    except BaseException as e:
        if os.path.exists(temp_path) and not safe_delete(temp_path):
            logger.warning("[SkillAdapter] 半成品清理失败: %s", temp_path)
        logger.error("[SkillAdapter] 打包失败: %s", e)
        raise
def partition_package_validation_errors(
        errors: list[str] | None) -> tuple[list[str], list[str], list[str]]:
    blocking_errors: list[str] = []
    crlf_errors: list[str] = []
    residue_errors: list[str] = []
    if isinstance(errors, str):
        errors = [errors]
    for error in errors or []:
        text = error if isinstance(error, str) else str(error)
        is_crlf = "CRLF 行尾符" in text
        is_residue = text.startswith("技能根存在运行态残留:")
        if is_crlf:
            crlf_errors.append(text)
        if is_residue:
            residue_errors.append(text)
        if not (is_crlf or is_residue):
            blocking_errors.append(text)
    return blocking_errors, crlf_errors, residue_errors
def package_skill(skill_dir: str, output_dir: str | None = None) -> str | None:
    skill_dir = _coerce_skill_packaging_dir(skill_dir)
    if skill_dir is None:
        return None
    ok, errors = validate_skill(skill_dir)
    blocking_errors, crlf_errors, residue_errors = (
        partition_package_validation_errors(errors))
    if blocking_errors or (not ok and not errors):
        logger.error("[SkillAdapter] 技能校验失败:")
        if not errors:
            logger.error("  - 校验未通过且未返回错误详情，拒绝交付未验证归档")
        for e in blocking_errors:
            logger.error("  - %s", e)
        return None
    if crlf_errors:
        logger.warning("[SkillAdapter] SKILL.md 为 CRLF，打包时将自动转换为 LF: %s",
                     skill_dir)
    for _residue in residue_errors:
        logger.warning("[SkillAdapter] 运行态残留不随包分发（已排除）: %s", _residue)
    output_path = _resolve_package_output(output_dir, skill_dir)
    if output_path is None:
        return None
    os.makedirs(os.path.dirname(output_path), exist_ok=True)
    _write_skill_archive(skill_dir, output_path)
    return output_path

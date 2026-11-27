from __future__ import annotations

import ast
import codecs
import copy
import io
import itertools
import json
import keyword
import logging
import math
import os
import re
import textwrap
import threading
import time
import tokenize
from collections import Counter
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_guard_io import (
    archive_backup,
    atomic_write_text,
    coerce_target_file,
    compile_error,
    decode_source_strict,
    detect_newline,
    format_diff_preview,
    resolve_within_root,
    split_tokenizer_lines,
)
from jwsgj.diag_guard_state import (
    rollback_note,
    write_with_rollback,
)
from jwsgj.diag_shared_ast_nodes import loop_body_has_break
from jwsgj.diag_shared_ast_views import parent_map
from jwsgj.diag_shared_source_core import (
    byte_col_to_char_col,
    check_comment_docstring_sync,
    parse_cached,
)
from jwsgj.diag_shared_source_scan import (
    identifier_tokens,
)
from jwsgj.diag_types_defs import (
    FeedbackModification,
    str_field,
)
from jwsgj.diag_types_normalize import (
    signal_bool,
    strip_bom,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_CONFIDENCE_FALLBACK,
    FMT_DATETIME,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    evolution_state_path,
    locked_artifact,
    read_evolution_section,
    write_evolution_section,
)
from jwsgj.runtime_scope import normalize_skill_dir

logger = logging.getLogger(__name__)
_LF = "\n"
_CRLF = "\r\n"
_DEFAULT_SKILL_DIR = ""
_DEFAULT_SOURCE_ENHANCEMENT_ID = ""
NESTED_BLOCK_TYPES = tuple(
    tp for tp in (
        ast.With, ast.For, ast.While, ast.Try, ast.If, ast.ExceptHandler,
        ast.AsyncWith, ast.AsyncFor, getattr(ast, "Match", None),
        getattr(ast, "TryStar", None),
    ) if tp is not None)
_TRY_OR_TRYSTAR: tuple = (ast.Try, getattr(ast, "TryStar", ast.Try))
_MATCH_TYPE = getattr(ast, "Match", None)
DEF_NAME_TYPES: tuple = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_MATCH_CAPTURE_TYPES: tuple = tuple(
    tp for tp in (getattr(ast, "MatchAs", None), getattr(ast, "MatchStar", None))
    if tp is not None)
_MATCH_MAPPING_TYPE = getattr(ast, "MatchMapping", None)
_TYPE_PARAM_TYPES: tuple = tuple(
    tp for tp in (getattr(ast, "TypeVar", None), getattr(ast, "ParamSpec", None),
                  getattr(ast, "TypeVarTuple", None))
    if tp is not None)
LOGIC_INJECTION_TEMPLATES: dict[str, dict[str, Any]] = {  # nosec E1-MUTABLE-GLOBAL — 注册表容器（register_injection_template 显式登记+覆盖告警可观测）  # jwsgj:suppress TP-07 — 审计认可：注册表容器（键控登记+覆盖告警可观测），非缺陷
    "path_normalize_check": {
        "description": "路径规范化+行号精确验证",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] 路径规范化验证 — 反哺增强
    import os
    if findings and os.name == "nt":
        for _f in findings:
            if isinstance(_f, dict) and isinstance(_f.get("file"), str):
                _f["file"] = _f["file"].replace("\\\\", "/")
                if "line" in _f and isinstance(_f["line"], int):
                    if _f["line"] < 0:
                        _f["line"] = 0
''',
    },
    "finding_description_enrichment": {
        "description": "增强finding描述的具体性",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] 描述增强 — 反哺增强
    if findings:
        for _f in findings:
            if isinstance(_f, dict) and isinstance(_f.get("description"), str):
                _desc = _f["description"]
                _vague = ["问题", "发现", "检测到", "存在",
                          "issue", "problem", "found", "detected", "exists"]
                if any(_v in _desc for _v in _vague) and len(_desc) < 20:
                    if "file" in _f:
                        _f["description"] = f"{_desc} (at {_f['file']})"
''',
    },
    "rollback_safety_check": {
        "description": "修复前安全检查，降低回滚率",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] 回滚安全检查 — 反哺增强
    import os
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _path = _f.get("file")
                if isinstance(_path, str) and _path and not os.path.isfile(_path):
                    _f["severity"] = _f.get("severity", "P2")
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("path-unverified")
''',
    },
    "side_effect_detection": {
        "description": "修复后副作用检测（AST对比）",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] 副作用检测 — 反哺增强
    import ast as _ast
    if findings and isinstance(findings, list):
        _checked = []
        for _f in findings:
            _fp = _f.get("file") if isinstance(_f, dict) else None
            if isinstance(_fp, str) and _fp:
                try:
                    with open(_fp, "r", encoding="utf-8", errors="ignore") as _fh:
                        _src = _fh.read()
                    _ast.parse(_src)  # 验证文件可解析
                except (SyntaxError, OSError, ValueError,
                        RecursionError, MemoryError):
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("target-unparseable")
            _checked.append(_f)
        findings[:] = _checked
''',
    },
    "null_check_guard": {
        "description": "None值防护检查，防止AttributeError",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] None guard
    if findings:
        for _f in findings:
            if (isinstance(_f, dict) and "value" in _f
                    and _f["value"] is None):
                if _f.get("severity", "P3") in ("P0", "P1"):
                    _f["severity"] = "P2"
''',
    },
    "duplicate_dedup": {
        "description": "重复finding去重，同file+line+rule_id只保留首个",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] Dedup
    if findings and isinstance(findings, list):
        _seen = set()
        _deduped = []
        for _f in findings:
            if (isinstance(_f, dict)
                    and all(_k in _f for _k in ("file", "line", "rule_id"))):
                _key = (str(_f["file"]), str(_f["line"]),
                        str(_f["rule_id"]))
                if _key in _seen:
                    continue
                _seen.add(_key)
            _deduped.append(_f)
        findings[:] = _deduped
''',
    },
    "severity_calibration": {
        "description": "基于文件路径的严重度校准",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] Severity calibration
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _fp = _f.get("file")
                _fp = _fp.replace("\\\\", "/") if isinstance(_fp, str) else ""
                _parts = [_part for _part in _fp.split("/") if _part]
                _is_test_path = any(
                    _part in ("test", "tests") for _part in _parts)
                _is_init_file = bool(_parts) and _parts[-1] in (
                    "__init__.py", "__init__.pyi")
                if _is_test_path or _is_init_file:
                    _cur = _f.get("severity", "P3")
                    if _cur in ("P0", "P1", "P2"):
                        _f["severity"] = "P3"
''',
    },
    "confidence_boost": {
        "description": "多源确认的finding置信度提升",
        "inject_point": "function_end",
        "code": '''
    # [auto-injected] Confidence boost
    import math as _math
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _src = _f.get("sources", [])
                if isinstance(_src, list) and len(_src) >= 3:
                    _conf = _f.get("confidence", 0.5)
                    if (isinstance(_conf, bool)
                            or not isinstance(_conf, (int, float))
                            or not _math.isfinite(_conf)):
                        _conf = 0.5
                    _conf = min(1.0, max(0.0, _conf))
                    _f["confidence"] = min(0.95, _conf + 0.1)
''',
    },
    "import_error_tag": {
        "description": "标记import相关finding并提升严重度",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Import error tag
    import re as _re
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                if _re.search(
                        r"(?<![a-z0-9])import(?:s|ed|ing|lib|errors?)?(?![a-z0-9])",
                        _msg):
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("import-related")
                    if _f.get("severity", "P3") == "P3":
                        _f["severity"] = "P2"
''',
    },
    "exception_safety_guard": {
        "description": "异常处理安全防护，标记裸except和过宽异常捕获",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Exception safety guard
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                if "bare except" in _msg or "except:" in _msg:
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("exception-safety")
                    if _f.get("severity", "P3") in ("P3", "P4"):
                        _f["severity"] = "P2"
                elif "except exception" in _msg and "specific" not in _msg:
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("broad-exception")
''',
    },
    "resource_cleanup_check": {
        "description": "资源清理检查，标记未关闭的文件和连接",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Resource cleanup check
    import math as _math
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                _resource_kw = ["open(", "close()", "with ", "contextlib"]
                if any(_kw in _msg for _kw in _resource_kw):
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("resource-cleanup")
                    _conf = _f.get("confidence", 0.5)
                    if (isinstance(_conf, bool)
                            or not isinstance(_conf, (int, float))
                            or not _math.isfinite(_conf)):
                        _conf = 0.5
                    _conf = min(1.0, max(0.0, _conf))
                    _f["confidence"] = min(0.95, _conf + 0.05)
''',
    },
    "type_validation_check": {
        "description": "类型验证检查，标记缺少类型检查的参数",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Type validation check
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                if "type" in _msg and ("check" in _msg or "annotation" in _msg):
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("type-validation")
''',
    },
    "encoding_safety_check": {
        "description": "编码安全检查，标记缺少encoding参数的文件操作",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Encoding safety check
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                if "encoding" in _msg or "utf-8" in _msg:
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("encoding-safety")
                    if _f.get("severity", "P3") == "P4":
                        _f["severity"] = "P3"
''',
    },
    "boundary_check_guard": {
        "description": "边界条件检查，标记缺少边界检查的循环和索引访问",
        "inject_point": "function_end",
        "code": r'''
    # [auto-injected] Boundary check guard
    import math as _math
    if findings:
        for _f in findings:
            if isinstance(_f, dict):
                _msg = f"{_f.get('message') or ''}{_f.get('description') or ''}".lower()
                _boundary_kw = ["index", "bound", "range", "len(", "slice"]
                if any(_kw in _msg for _kw in _boundary_kw):
                    if not isinstance(_f.get("tags"), list):
                        _f["tags"] = []
                    _f["tags"].append("boundary-check")
                    _conf = _f.get("confidence", 0.5)
                    if (isinstance(_conf, bool)
                            or not isinstance(_conf, (int, float))
                            or not _math.isfinite(_conf)):
                        _conf = 0.5
                    _conf = min(1.0, max(0.0, _conf))
                    _f["confidence"] = min(0.95, _conf + 0.05)
''',
    },
}
_L2_KEYWORD_FALLBACK = (
    (("路径", "规范化", "normalize"), "path_normalize_check"),
    (("描述", "模糊", "vague"), "finding_description_enrichment"),
    (("回滚", "行号", "rollback"), "rollback_safety_check"),
    (("副作用", "ast", "side"), "side_effect_detection"),
    (("none", "空值", "null"), "null_check_guard"),
    (("重复", "去重", "duplicate"), "duplicate_dedup"),
    (("严重", "校准", "severity"), "severity_calibration"),
    (("置信", "confidence", "多源"), "confidence_boost"),
    (("import", "导入"), "import_error_tag"),
    (("异常", "except", "exception"), "exception_safety_guard"),
    (("资源", "resource", "close"), "resource_cleanup_check"),
    (("类型", "type", "annotation"), "type_validation_check"),
    (("编码", "encoding", "unicode"), "encoding_safety_check"),
    (("边界", "bound", "index"), "boundary_check_guard"),
)
def match_l2_template(description: str, entry: dict) -> str:
    if not isinstance(description, str):
        description = ""
    if not isinstance(entry, dict):
        entry = {}
    description = description.lower()
    for matcher in (_match_exact_template, _match_keyword_fallback):
        matched = matcher(description)
        if matched is not None:
            return matched
    return _default_template_for(entry)
_CJK_ROUTING_TOKEN_RE = re.compile(r"[\u4e00-\u9fff]{3,}")
def _contains_token(text: str, token: str, *,
                    ident: bool = False) -> bool:
    if not isinstance(text, str) or not isinstance(token, str) or not token:
        return False
    if token.isascii():
        left = r"(?<![A-Za-z0-9_])" if ident else r"(?<![A-Za-z0-9])"
        right = r"(?![A-Za-z0-9_])" if ident else r"(?![A-Za-z0-9])"
        return re.search(
            rf"{left}{re.escape(token)}{right}", text) is not None
    return token in text
def _template_name_ok(name: object) -> bool:
    if not isinstance(name, str) or not name.strip():
        return False
    return all(ch.isprintable() for ch in name)
def _template_matches(tmpl_name: object, tmpl: object,
                      description: str) -> bool:
    if not isinstance(tmpl_name, str):
        return False
    name = tmpl_name.lower()
    description = description.lower()
    if _contains_token(description, name, ident=True):
        return True
    tmpl_desc = tmpl.get("description") if isinstance(tmpl, dict) else None
    if not isinstance(tmpl_desc, str):
        return False
    return any(
        _contains_token(description, token)
        for token in _CJK_ROUTING_TOKEN_RE.findall(tmpl_desc.lower()))
def _match_exact_template(description: str) -> str | None:
    return next((
        tmpl_name
        for tmpl_name, tmpl in tuple(LOGIC_INJECTION_TEMPLATES.items())
        if _template_matches(tmpl_name, tmpl, description)
    ), None)
def _match_keyword_fallback(description: str) -> str | None:
    for keywords, tmpl_name in _L2_KEYWORD_FALLBACK:
        if any(_contains_token(description, kw) for kw in keywords):
            return tmpl_name
    return None
_DEFAULT_TEMPLATE_RULES: tuple[tuple[str, str], ...] = (
    ("import", "import_error_tag"),
    ("导入", "import_error_tag"),
    ("exception", "exception_safety_guard"),
    ("error", "exception_safety_guard"),
    ("异常", "exception_safety_guard"),
    ("错误", "exception_safety_guard"),
    ("resource", "resource_cleanup_check"),
    ("file", "resource_cleanup_check"),
    ("资源", "resource_cleanup_check"),
    ("文件", "resource_cleanup_check"),
    ("type", "type_validation_check"),
    ("类型", "type_validation_check"),
    ("encoding", "encoding_safety_check"),
    ("编码", "encoding_safety_check"),
    ("boundary", "boundary_check_guard"),
    ("边界", "boundary_check_guard"),
)
_DEFAULT_TEMPLATE_FALLBACK = "duplicate_dedup"
def _default_template_for(entry: dict) -> str:
    sev = (str_field(entry, "severity") or "P3").strip().upper()
    cat = str_field(entry, "category").lower()
    if sev in ("P0", "P1"):
        return "null_check_guard"
    for kw, template in _DEFAULT_TEMPLATE_RULES:
        if _contains_token(cat, kw):
            return template
    return _DEFAULT_TEMPLATE_FALLBACK
def _resolve_injection_prefix(
        file_hint: str, func_hint: str, entry: dict | None,
        aliases: Mapping[str, str | None] | None,
) -> tuple[str, str] | None:
    if not isinstance(aliases, Mapping) or file_hint not in aliases:
        return None
    target_file = aliases[file_hint]
    if target_file is None:
        entry = entry if isinstance(entry, dict) else {}
        entry_file = str_field(entry, "target_file")
        entry_func = str_field(entry, "target_func")
        return (entry_file, entry_func or func_hint) if entry_file else ("", "")
    if not isinstance(target_file, str):
        return "", ""
    target_file = target_file.strip()
    return (target_file, func_hint) if target_file else ("", "")
def parse_injection_target(
        target: str, entry: dict | None = None,
        aliases: Mapping[str, str | None] | None = None,
) -> tuple[str, str]:
    if not isinstance(target, str):
        target = ""
    sep = next((s for s in ("::", "/") if s in target), "")
    if not sep:
        return "", ""
    file_hint, _, func_part = target.partition(sep)
    file_hint, func_hint = file_hint.strip(), func_part.strip()
    resolved = _resolve_injection_prefix(file_hint, func_hint, entry, aliases)
    if resolved is not None:
        return resolved
    return (file_hint, func_hint) if sep == "::" else ("", "")
TEMPLATE_FAILURE_THRESHOLD = 3
TEMPLATE_RECOVERY_COOLDOWN_S = 3600.0
DEFAULT_INJECT_POINT = "function_end"
_VALID_INJECT_POINTS = frozenset({DEFAULT_INJECT_POINT})
TEMPLATE_META_PATH_ENV_VAR = "JWSGJ_TEMPLATE_META_PATH"
_TEMPLATE_META: dict[str, dict[str, Any]] = {}
_META_PATH_WARNED = False
_ENV_OVERRIDE = os.environ.get(TEMPLATE_META_PATH_ENV_VAR, "").strip()
if _ENV_OVERRIDE and not os.path.isabs(os.path.normpath(_ENV_OVERRIDE)):
    raise ValueError(
        f"{TEMPLATE_META_PATH_ENV_VAR}={_ENV_OVERRIDE!r} 必须是绝对路径"
        f"（统计文件完整路径）；相对路径会被拼接到当前目录，"
        "可能在意外的位置创建统计文件")
_TEMPLATE_META_PATH = _ENV_OVERRIDE or None
_PROCESS_META_KEY = "process"
_PROJECT_TEMPLATE_META: dict[str, dict[str, dict[str, Any]]] = {}
_PROJECT_TEMPLATE_META_LOADED: set[str] = set()
_PROJECT_TEMPLATE_META_WARNED: set[str] = set()
_TEMPLATE_META_MEMORY_LOCK = threading.RLock()
@dataclass(frozen=True)
class _TemplateMetaContext:
    key: str
    meta: dict[str, dict[str, Any]]
    path: str | None
    legacy: bool
def _template_meta_path(skill_dir: str) -> str | None:
    if _ENV_OVERRIDE:
        return _ENV_OVERRIDE
    if not skill_dir:
        return None
    try:
        evolution_state_path(skill_dir)
        return "template_meta"
    except (OSError, RuntimeError, ValueError) as e:
        logger.warning(
            "[TemplateMeta] 目标项目 jinhua 目录不可用，模板统计降级为仅内存: %s", e)
        return None
def _template_meta_context(skill_dir: str = _DEFAULT_SKILL_DIR) -> _TemplateMetaContext:
    if _ENV_OVERRIDE:
        return _TemplateMetaContext(
            _PROCESS_META_KEY, _TEMPLATE_META, _TEMPLATE_META_PATH, True)
    skill_dir = coerce_target_file(skill_dir)
    if not skill_dir:
        return _TemplateMetaContext(
            _PROCESS_META_KEY, _TEMPLATE_META, _TEMPLATE_META_PATH, True)
    root = normalize_skill_dir(skill_dir)
    key = os.path.normcase(os.path.realpath(root))
    meta = _PROJECT_TEMPLATE_META.setdefault(key, {})
    context = _TemplateMetaContext(
        key, meta, _template_meta_path(root), False)
    if key not in _PROJECT_TEMPLATE_META_LOADED:
        _PROJECT_TEMPLATE_META_LOADED.add(key)
        _load_template_meta(root)
    return context
def _load_template_meta(skill_dir: str = _DEFAULT_SKILL_DIR) -> None:
    context = _template_meta_context(skill_dir)
    path = context.path
    if not path:
        return
    try:
        if context.legacy:
            if not os.path.isfile(path):
                return
            with open(path, encoding="utf-8-sig") as f:  # jwsgj:suppress TAINT — 审计认可：path 来自环境覆盖（已强制绝对路径）
                data = json.load(f)
        else:
            data = read_evolution_section(skill_dir, "template_meta")
            if data is None:
                return
        if not isinstance(data, dict):
            logger.warning(
                "[TemplateMeta] %s 内容非 dict（%s），忽略该统计",
                path, type(data).__name__)
            return
        context.meta.clear()
        context.meta.update(data)
        if _migrate_legacy_meta(context.meta):
            _save_template_meta(skill_dir)
    except (OSError, ValueError, RecursionError) as e:
        logger.debug("JSON 解析失败（跳过）: %s", e)
@contextmanager
def _template_meta_transaction(
        skill_dir: str, *, refresh: bool = False,
) -> Iterator[tuple[_TemplateMetaContext, bool]]:
    context = _template_meta_context(skill_dir)
    if not context.path:
        with _TEMPLATE_META_MEMORY_LOCK:
            yield context, True
        return
    path = context.path if context.legacy else evolution_state_path(skill_dir)
    with locked_artifact(path) as locked:
        if not locked:
            logger.warning(
                "[TemplateMeta] 跨进程锁不可用，模板统计仅更新当前进程内存: %s",
                path)
            yield context, False
            return
        if refresh:
            _load_template_meta(skill_dir)
        yield context, True
def _migrate_legacy_meta(meta_container: dict | None = None) -> bool:
    migrated = False
    now = time.time()
    legacy_defaults = (
        ("consecutive_failures", TEMPLATE_FAILURE_THRESHOLD),
        ("disabled_since", now),
    )
    container = _TEMPLATE_META if meta_container is None else meta_container
    for meta in container.values():
        if not isinstance(meta, dict) or not signal_bool(meta.get("disabled")):
            continue
        for key, value in legacy_defaults:
            if key not in meta:
                meta[key] = value
                migrated = True
    return migrated
def _save_template_meta(
        skill_dir: str = _DEFAULT_SKILL_DIR, dirty_name: str = "") -> None:
    with _template_meta_transaction(skill_dir) as (context, can_persist):
        if can_persist:
            _save_template_meta_locked(skill_dir, context, dirty_name)
def _save_template_meta_locked(
        skill_dir: str, context: _TemplateMetaContext, dirty_name: str,
) -> None:
    global _META_PATH_WARNED
    path = context.path
    if not path:
        if context.legacy:
            if not _META_PATH_WARNED:
                logger.warning(
                    "[TemplateMeta] 无可用持久化路径（jinhua 归口降级），"
                    "后续跳过落盘且不再逐次告警")
                _META_PATH_WARNED = True
        elif context.key not in _PROJECT_TEMPLATE_META_WARNED:
            logger.warning(
                "[TemplateMeta] 目标项目无可用持久化路径，后续仅使用内存统计: %s",
                context.key)
            _PROJECT_TEMPLATE_META_WARNED.add(context.key)
        return
    try:
        persisted = None
        if context.legacy:
            if os.path.isfile(path):
                with open(path, encoding="utf-8-sig") as f:
                    persisted = json.load(f)
        else:
            persisted = read_evolution_section(skill_dir, "template_meta")
        if persisted is not None and not isinstance(persisted, dict):
            logger.warning(
                "[TemplateMeta] %s 磁盘基线非 dict（%s），拒绝覆盖统计文件",
                path, type(persisted).__name__)
            return
        if isinstance(persisted, dict):
            merged = dict(persisted)
            for key, value in context.meta.items():
                if (not dirty_name or key == dirty_name
                        or key not in merged):
                    merged[key] = value
            context.meta.clear()
            context.meta.update(merged)
        if context.legacy:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            atomic_write_text(
                path,
                json.dumps(context.meta, ensure_ascii=False, indent=2,
                           default=str),
                tag="template_meta",
            )
        elif not write_evolution_section(
                skill_dir, "template_meta", context.meta):
            logger.warning(
                "[TemplateMeta] 模板统计 section 落盘失败: %s", skill_dir)
    except (OSError, TypeError, ValueError, RecursionError) as e:
        logger.warning(
            "[TemplateMeta] 模板统计持久化失败: %s — %s", path, e)
def _reset_breaker(meta: dict) -> None:
    meta["consecutive_failures"] = 0
    meta["disabled"] = False
    meta["disabled_since"] = 0.0
def _fresh_meta(source: str) -> dict:
    meta = {
        "applications": 0,
        "successes": 0,
        "failures": 0,
        "source": source,
    }
    _reset_breaker(meta)
    return meta
def as_text(value: object) -> str:
    return value if isinstance(value, str) else ""
def _template_source(name: str) -> str:
    template = LOGIC_INJECTION_TEMPLATES.get(name)
    if isinstance(template, dict):
        source = template.get("source")
        if isinstance(source, str) and source.strip():
            return source
    return "builtin"
def record_template_application(name: str, success: bool, skill_dir: str = _DEFAULT_SKILL_DIR) -> None:
    name = as_text(name)
    if not _template_name_ok(name):
        logger.debug("[TemplateMeta] 模板名非法或为空，跳过使用统计记录")
        return
    with _template_meta_transaction(skill_dir, refresh=True) as (context, can_persist):
        container = context.meta
        meta = container.get(name)
        if not isinstance(meta, dict):
            meta = _fresh_meta(_template_source(name))
            container[name] = meta
        meta["applications"] = _safe_count(meta, "applications") + 1
        if success:
            _apply_success_meta(meta, name, skill_dir)
            logger.info(
                "[TemplateMeta] 模板注入应用成功: %s (skill_dir=%s)",
                name, skill_dir,
                extra={"event": "template_applied"})
        else:
            _apply_failure_meta(meta, name, skill_dir)
            logger.info(
                "[TemplateMeta] 模板注入应用失败: %s (连续第 %d 次, skill_dir=%s)",
                name, meta["consecutive_failures"], skill_dir,
                extra={"event": "template_apply_failed"})
        if can_persist:
            _save_template_meta(skill_dir, name)
def _safe_count(meta: dict, key: str) -> int:
    value = meta.get(key)
    if isinstance(value, bool):
        return 0
    try:
        return max(0, int(value or 0))
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_safe_count:coerce')
        return 0
def _apply_success_meta(meta: dict, name: str, skill_dir: str) -> None:
    _was_disabled = signal_bool(meta.get("disabled"))
    meta["successes"] = _safe_count(meta, "successes") + 1
    _reset_breaker(meta)
    if _was_disabled:
        logger.info(
            "[TemplateMeta] 模板 %s 半开试探成功，解除熔断恢复正常注入"
            " (skill_dir=%s)", name, skill_dir)
def _apply_failure_meta(meta: dict, name: str, skill_dir: str) -> None:
    meta["failures"] = _safe_count(meta, "failures") + 1
    consecutive = _safe_count(meta, "consecutive_failures") + 1
    meta["consecutive_failures"] = consecutive
    if consecutive >= TEMPLATE_FAILURE_THRESHOLD:
        meta["disabled"] = True
        meta["disabled_since"] = time.time()
        logger.warning(
            "[TemplateMeta] 模板 %s 连续失败 %d 次达熔断阈值，自动禁用"
            "（冷却 %.0fs 后半开试探，skill_dir=%s）",
            name, consecutive, TEMPLATE_RECOVERY_COOLDOWN_S, skill_dir)
def get_template_stats(name: str = "", skill_dir: str = _DEFAULT_SKILL_DIR) -> dict:
    name = as_text(name)
    with _template_meta_transaction(skill_dir, refresh=True) as (context, _can_persist):
        container = context.meta
        if name:
            v = container.get(name)
            return dict(v) if isinstance(v, dict) else {}
        return {k: dict(v) for k, v in container.items()
                if isinstance(v, dict)}
def is_template_disabled(name: str, skill_dir: str = _DEFAULT_SKILL_DIR) -> bool:
    name = as_text(name)
    with _template_meta_transaction(skill_dir, refresh=True) as (context, _can_persist):
        v = context.meta.get(name)
        if not isinstance(v, dict) or not signal_bool(v.get("disabled")):
            return False
        _raw_since = v.get("disabled_since")
        if isinstance(_raw_since, bool):
            return True
        try:
            since = float(_raw_since)
        except (TypeError, ValueError, OverflowError) as _e:
            log_swallowed(__name__, _e, context='is_template_disabled:TypeError')
            since = time.time()
        if not math.isfinite(since):
            return True
        return (time.time() - since) < TEMPLATE_RECOVERY_COOLDOWN_S
def register_injection_template(
    name: str,
    description: str,
    code: str,
    inject_point: str = DEFAULT_INJECT_POINT,
    skill_dir: str = _DEFAULT_SKILL_DIR,
    source: str = "agent",
) -> bool:
    if not _register_params_ok(name, description, code, inject_point):
        return False
    if not _code_syntax_ok(name, code):
        return False
    _warn_overwrite(name, source)
    template = {
        "description": description,
        "inject_point": inject_point,
        "code": code,
        "source": source,
        "created_at": time.strftime(FMT_DATETIME),
    }
    logger.info(
        "[TemplateMeta] 注册自定义注入模板 %s (source=%s, skill_dir=%s)",
        name, source, skill_dir)
    LOGIC_INJECTION_TEMPLATES[name] = template
    _prepare_template_meta(name, source, skill_dir)
    return True
def _register_params_ok(name: str, description: str, code: str,
                        inject_point: str) -> bool:
    if not _template_name_ok(name):
        logger.warning(
            "[TemplateMeta] 模板名注册被拒：需为非空字符串且不含换行/"
            "控制字符（模板名会拼入注入标记行）: %r", name)
        return False
    for value in (description, code):
        if not isinstance(value, str) or not value.strip():
            return False
    if not isinstance(inject_point, str) or inject_point not in _VALID_INJECT_POINTS:
        logger.warning(
            "[TemplateMeta] 模板 %s 注册被拒：inject_point=%r "
            "不在合法值域 %s", name, inject_point,
            sorted(_VALID_INJECT_POINTS))
        return False
    return True
def _code_syntax_ok(name: str, code: str) -> bool:
    try:
        compile(
            "def _tpl_syntax_probe():\n"
            + textwrap.indent(textwrap.dedent(code).strip(), "    ")
            + "\n",
            f"<template:{name}>",
            "exec",
        )
    except PARSE_DEGRADE_EXC as e:
        logger.warning(
            "[TemplateMeta] 模板 %s 注册被拒：code 未通过函数体语法校验，"
            "无法作为函数体语句序列注入: %s", name, e)
        return False
    template_tree = parse_template_code(code)
    if template_tree is not None and any(
            _stmt_has_runtime_yield(stmt) for stmt in template_tree.body):
        logger.warning(
            "[TemplateMeta] 模板 %s 注册被拒：yield/yield from 会改变"
            "目标函数的调用契约，禁止注入", name)
        return False
    if template_tree is not None and any(
            _stmt_has_runtime_return(stmt) for stmt in template_tree.body):
        logger.warning(
            "[TemplateMeta] 模板 %s 注册被拒：return 会绕过"
            "目标函数原有返回契约，禁止注入", name)
        return False
    return True
def _warn_overwrite(name: str, source: str) -> None:
    if name in LOGIC_INJECTION_TEMPLATES:
        _existing = LOGIC_INJECTION_TEMPLATES[name]
        _old_source = (_existing.get("source", "unknown")
                       if isinstance(_existing, dict) else "corrupted(non-dict)")
        logger.warning(
            "[TemplateMeta] 模板 %s 已存在，本次注册将覆盖既有模板"
            " (old_source=%s, new_source=%s；历史统计保留累计计数，"
            "熔断状态复位)",
            name, _old_source, source)
def _prepare_template_meta(
        name: str, source: str, skill_dir: str = _DEFAULT_SKILL_DIR) -> None:
    with _template_meta_transaction(skill_dir, refresh=True) as (context, can_persist):
        container = context.meta
        _existing_meta = container.get(name)
        if isinstance(_existing_meta, dict):
            for _cnt_key in ("applications", "successes", "failures"):
                _v = _existing_meta.get(_cnt_key)
                if isinstance(_v, bool) or not isinstance(_v, int) or _v < 0:
                    _existing_meta[_cnt_key] = 0
            _reset_breaker(_existing_meta)
            _existing_meta["source"] = source
        else:
            container[name] = _fresh_meta(source)
        if can_persist:
            _save_template_meta(skill_dir, name)
if _TEMPLATE_META_PATH:
    _load_template_meta()
def _if_is_terminating(stmt: ast.If) -> bool:
    orelse = stmt.orelse
    return (bool(stmt.body) and bool(orelse)
            and _stmt_is_terminating(stmt.body[-1])
            and _stmt_is_terminating(orelse[-1]))
def _try_is_terminating(stmt: ast.AST) -> bool:
    finalbody = getattr(stmt, "finalbody", None) or []
    if finalbody and _stmt_is_terminating(finalbody[-1]):
        return True
    body_exits = bool(stmt.body) and _stmt_is_terminating(stmt.body[-1])
    if not body_exits:
        orelse = getattr(stmt, "orelse", None) or []
        if not (orelse and _stmt_is_terminating(orelse[-1])):
            return False
    return all(
        bool(h.body) and _stmt_is_terminating(h.body[-1])
        for h in stmt.handlers)
def _match_is_terminating(stmt: ast.AST) -> bool:
    cases = getattr(stmt, "cases", None) or []
    if not cases:
        return False
    last_case = cases[-1]
    if getattr(last_case, "guard", None) is not None:
        return False
    pattern = getattr(last_case, "pattern", None)
    if not (isinstance(pattern, ast.MatchAs) and pattern.pattern is None):
        return False
    return all(
        bool(case.body) and _stmt_is_terminating(case.body[-1])
        for case in cases)
def _with_is_terminating(stmt: ast.AST) -> bool:
    return (bool(stmt.body)
            and _stmt_is_terminating(stmt.body[-1]))
def _while_is_terminating(stmt: ast.While) -> bool:
    test = stmt.test
    if not (isinstance(test, ast.Constant) and test.value):
        return False
    return not loop_body_has_break(stmt.body)
def _stmt_is_terminating(stmt: ast.AST) -> bool:
    if isinstance(stmt, (ast.Return, ast.Raise)):
        return True
    if isinstance(stmt, ast.If):
        return _if_is_terminating(stmt)
    if isinstance(stmt, ast.While):
        return _while_is_terminating(stmt)
    if isinstance(stmt, _TRY_OR_TRYSTAR):
        return _try_is_terminating(stmt)
    if _MATCH_TYPE is not None and isinstance(stmt, _MATCH_TYPE):
        return _match_is_terminating(stmt)
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        return _with_is_terminating(stmt)
    return False
def _function_qualname(node: ast.AST, parents: dict) -> str:
    parts = [node.name]
    current = parents.get(node)
    while current is not None:
        if isinstance(current, DEF_NAME_TYPES):
            parts.append(current.name)
        current = parents.get(current)
    return ".".join(reversed(parts))
def find_function_def(tree: ast.AST, func_name: str) -> ast.AST | None:
    if not isinstance(func_name, str) or not func_name:
        return None
    parents = parent_map(tree)
    exact: list[tuple[str, ast.AST]] = []
    suffixed: list[tuple[str, ast.AST]] = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        qualname = _function_qualname(node, parents)
        if qualname == func_name:
            exact.append((qualname, node))
        elif qualname.endswith("." + func_name):
            suffixed.append((qualname, node))
    matches = exact or suffixed
    if len(matches) > 1:
        logger.warning(
            "[L2] 目标函数名 %r 匹配到 %d 个定义（%s），无法确定注入目标，"
            "拒绝按遍历顺序择一", func_name, len(matches),
            ", ".join(sorted(name for name, _node in matches)))
        return None
    return matches[0][1] if matches else None
def function_has_inline_body(source: str, func_node: ast.AST) -> bool:
    body = getattr(func_node, "body", None) or []
    if not body:
        return False
    first_stmt = body[0]
    lines = split_tokenizer_lines(source)
    row = getattr(first_stmt, "lineno", 0) - 1
    byte_col = getattr(first_stmt, "col_offset", -1)
    if not 0 <= row < len(lines):
        return True
    raw_line = lines[row].encode("utf-8")
    if not 0 <= byte_col <= len(raw_line):
        return True
    prefix = raw_line[:byte_col].decode("utf-8", errors="ignore")
    return bool(prefix.strip())
def find_function_end(source: str,
                       func_name: str) -> int | None:
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[CodeFeedback] AST解析失败,返回None: %s", e)
        return None
    func_node = find_function_def(tree, func_name)
    if func_node is None or not func_node.body:
        return None
    if function_has_inline_body(source, func_node):
        logger.warning(
            "[L2] 函数 %s 的首个函数体语句与 def 签名同行，"
            "无安全行级注入点", func_node.name)
        return None
    return _locate_inject_line(func_node)
def _stmt_has_runtime_yield(stmt: ast.AST) -> bool:
    if isinstance(stmt, (ast.Yield, ast.YieldFrom)):
        return True
    if isinstance(stmt, (*DEF_NAME_TYPES, ast.Lambda)):
        return False
    return any(_stmt_has_runtime_yield(child)
               for child in ast.iter_child_nodes(stmt))
def _stmt_has_runtime_return(stmt: ast.AST) -> bool:
    if isinstance(stmt, ast.Return):
        return True
    if isinstance(stmt, (*DEF_NAME_TYPES, ast.Lambda)):
        return False
    return any(_stmt_has_runtime_return(child)
               for child in ast.iter_child_nodes(stmt))
def _locate_inject_line(
        func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> int | None:
    last_stmt = func_node.body[-1]
    if any(_stmt_has_runtime_return(stmt) for stmt in func_node.body[:-1]):
        logger.warning(
            "[L2] 函数 %s 在函数尾注入点之前存在提前 return，"
            "无统一安全注入点，拒绝产生绕过路径", func_node.name)
        return None
    if _stmt_is_terminating(last_stmt):
        if len(func_node.body) > 1:
            previous = func_node.body[-2]
            previous_end = (getattr(previous, "end_lineno", previous.lineno)
                            or previous.lineno)
            if previous_end >= last_stmt.lineno:
                logger.warning(
                    "[L2] 函数 %s 的尾语句与前一条语句共用行 %d，"
                    "无法按行只在尾语句前注入，拒绝改变执行顺序",
                    func_node.name, last_stmt.lineno)
                return None
        return last_stmt.lineno - 1
    if _stmt_has_runtime_return(last_stmt):
        logger.warning(
            "[L2] 函数 %s 的尾语句仅部分执行路径 return，"
            "无覆盖全部返回路径的安全注入点，拒绝注入", func_node.name)
        return None
    end_line = _find_stmt_end_line(last_stmt)
    if end_line is not None:
        return end_line
    return None
def _find_stmt_end_line(node: ast.AST) -> int | None:
    if getattr(node, 'end_lineno', None):
        return node.end_lineno
    for child in ast.iter_child_nodes(node):
        result = _find_stmt_end_line(child)
        if result is not None:
            return result
    return None
def _extract_body_indent(source: str, node: ast.AST) -> str:
    default_indent = " " * (getattr(node, "col_offset", 0) + 4)
    body = getattr(node, "body", None)
    if not body:
        return default_indent
    lines = split_tokenizer_lines(source)
    idx = getattr(body[0], "lineno", 0) - 1
    if 0 <= idx < len(lines):
        line = lines[idx]
        indent = line[:len(line) - len(line.lstrip())]
        if indent:
            return indent
    return default_indent
def indent_code(code: str, target_func: str,
                 source: str) -> str:
    code = as_text(code)
    func_indent = "    "
    try:
        tree = parse_cached(source)
        func_node = find_function_def(tree, target_func)
        if func_node is not None:
            func_indent = _extract_body_indent(source, func_node)
    except PARSE_DEGRADE_EXC:
        logger.warning("[L2] 缩进定位 AST 解析失败，按默认 4 空格: %s",
                       target_func)
    code = textwrap.dedent(code)
    result_lines = []
    for line in split_tokenizer_lines(code):
        core = line.rstrip("\r\n")
        if core.strip():
            result_lines.append(func_indent + core)
        else:
            result_lines.append("")
    result_lines.append("")
    return "\n".join(result_lines) + "\n"
def binding_sites(node: ast.AST) -> list:
    sites: list = []
    if isinstance(node, (ast.ExceptHandler, *DEF_NAME_TYPES)):
        sites.append((node.name, "token"))
    elif isinstance(node, (ast.Global, ast.Nonlocal)):
        sites.extend((name, "token") for name in node.names)
    elif isinstance(node, _MATCH_CAPTURE_TYPES):
        sites.append((node.name, "tail"))
    elif _MATCH_MAPPING_TYPE is not None and isinstance(node, _MATCH_MAPPING_TYPE):
        sites.append((node.rest, "rest"))
    elif isinstance(node, _TYPE_PARAM_TYPES):
        sites.append((node.name, "head"))
    return [(name, kind) for name, kind in sites if isinstance(name, str)]
def _is_local_underscore_name(name: object) -> bool:
    if not isinstance(name, str) or not name.startswith("_"):
        return False
    if name == "_":
        return False
    return not (name.startswith("__") and name.endswith("__"))
def _is_conflict_name(name: object) -> bool:
    return (isinstance(name, str) and name.isidentifier()
            and not keyword.iskeyword(name))
def _collect_scope_names(root: ast.AST, name_ok) -> set:
    names: set = set()
    for child in walk_nodes(root):
        if isinstance(child, ast.Name) and name_ok(child.id):
            names.add(child.id)
        elif isinstance(child, ast.arg) and name_ok(child.arg):
            names.add(child.arg)
        elif isinstance(child, (ast.Import, ast.ImportFrom)):
            names |= _import_bound_names(child, name_ok)
        else:
            names.update(name for name, _kind in binding_sites(child)
                         if name_ok(name))
    return names
def _import_bound_names(node: ast.Import | ast.ImportFrom, name_ok) -> set:
    bound_names: set = set()
    for alias in node.names:
        bound = alias.asname or alias.name.split(".")[0]
        if name_ok(bound):
            bound_names.add(bound)
    return bound_names
def _wrap_template_scope(template_code: str) -> str:
    body = textwrap.indent(
        textwrap.dedent(template_code).strip(), "        ")
    return (
        "    _l2_scope = locals()\n"
        "    _l2_items = (_l2_scope[\"findings\"] if \"findings\" in _l2_scope\n"
        "                 else next((_v for _v in _l2_scope.values()\n"
        "                            if isinstance(_v, list) and _v\n"
        "                            and isinstance(_v[0], dict)), None))\n"
        "    if isinstance(_l2_items, list) and _l2_items:\n"
        "        findings = _l2_items\n"
        + body + "\n"
    )
def parse_template_code(template_code: str) -> ast.Module | None:
    text = textwrap.dedent(as_text(template_code)).strip()
    if not text:
        return None
    try:
        return parse_cached(text)
    except PARSE_DEGRADE_EXC:
        try:
            return parse_cached(_wrap_function_body(text))
        except PARSE_DEGRADE_EXC as e:
            logger.warning("[CodeFeedback] 模板AST解析失败: %s", e)
            return None
def _parse_conflict_sources(source: str, template_code: str):
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[CodeFeedback] 源码AST解析失败: %s", e)
        return None
    tmpl_tree = parse_template_code(template_code)
    if tmpl_tree is None:
        return None
    return tree, tmpl_tree
def detect_variable_conflicts(source: str, func_name: str,
                               template_code: str) -> tuple:
    parsed = _parse_conflict_sources(source, template_code)
    if parsed is None:
        return False, {}
    tree, tmpl_tree = parsed
    parents = parent_map(tree)
    target_node = find_function_def(tree, func_name)
    existing_names = _collect_visible_names(
        tree, target_node, parents, _is_conflict_name)
    template_names = _collect_scope_names(tmpl_tree, _is_conflict_name)
    renameable_names = _local_shape_names(
        tmpl_tree, name_ok=_is_conflict_name)
    conflicts = existing_names & renameable_names
    captured = _template_capture_conflicts(
        target_node, parents, template_names - renameable_names)
    if not conflicts and not captured:
        return False, {}
    rename_map = _build_rename_map(conflicts, existing_names, template_names)
    if rename_map:
        logger.info("[L2] 检测到 %d 个变量名冲突, 重命名映射: %s",
                     len(rename_map), rename_map)
    if captured:
        logger.warning("[L2] 模板自由变量被目标局部/闭包绑定捕获: %s",
                       sorted(captured))
    return True, rename_map
def _collect_visible_names(tree: ast.Module, target_node: ast.AST | None,
                           parents: dict, name_ok) -> set:
    existing_names: set = set()
    if target_node is None:
        return existing_names
    existing_names |= _collect_scope_names(target_node, name_ok)
    cur = parents.get(target_node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            existing_names |= _collect_scope_names(cur, name_ok)
        cur = parents.get(cur)
    for stmt in tree.body:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            if name_ok(stmt.name):
                existing_names.add(stmt.name)
            continue
        existing_names |= _collect_scope_names(stmt, name_ok)
    return existing_names
def _direct_global_names(root: ast.AST) -> set[str]:
    names: set[str] = set()
    pending = [root]
    while pending:
        child = pending.pop()
        if child is not root and isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(child, ast.Global):
            names.update(child.names)
        pending.extend(ast.iter_child_nodes(child))
    return names
def _template_capture_conflicts(target_node: ast.AST | None,
                                parents: dict, free_names: set) -> set:
    if target_node is None or not free_names:
        return set()
    target_locals = _local_shape_names(
        target_node, name_ok=_is_conflict_name)
    target_locals.discard(target_node.name)
    visible_bindings = set(target_locals)
    cur = parents.get(target_node)
    while cur is not None:
        if isinstance(cur, (ast.FunctionDef, ast.AsyncFunctionDef)):
            outer_locals = _local_shape_names(cur, name_ok=_is_conflict_name)
            outer_locals.discard(cur.name)
            visible_bindings |= outer_locals
        cur = parents.get(cur)
    visible_bindings -= _direct_global_names(target_node)
    return free_names & visible_bindings
def _build_rename_map(conflicts: set, existing_names: set,
                      template_names: set) -> dict:
    rename_map = {}
    for name in conflicts:
        new_name = name + "_inj"
        while new_name in existing_names or new_name in template_names:
            new_name += "x"
        rename_map[name] = new_name
    return rename_map
def underscore_mentions(tree: ast.AST) -> set:
    names: set = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.Name) and node.id.startswith("_"):
            names.add(node.id)
        elif isinstance(node, ast.Attribute) and node.attr.startswith("_"):
            names.add(node.attr)
    return names
def _valid_rename_pair(old: object, new: object) -> bool:
    return (isinstance(old, str) and old.isidentifier()
            and isinstance(new, str) and new.isidentifier()
            and not keyword.iskeyword(new))
def clean_rename_map(rename_map: dict) -> dict:
    if not isinstance(rename_map, dict):
        return {}
    return {
        old: new for old, new in rename_map.items()
        if _valid_rename_pair(old, new)
    }
def parse_renameable(text: str) -> tuple:
    for candidate, wrapper_shift in ((text, 0), (_wrap_function_body(text), 1)):
        try:
            return (parse_cached(candidate), (4 if wrapper_shift else 0),
                    wrapper_shift, candidate)
        except PARSE_DEGRADE_EXC as _e:
            if wrapper_shift:
                log_swallowed(__name__, _e, context='_parse_renameable:degrade')
            continue
    return None, 0, 0, text
def _wrap_function_body(text: str) -> str:
    return "def _tpl_rename_probe():\n" + textwrap.indent(text, "    ")
def _printed_span(node: ast.AST, base_col: int,
                  line_shift: int) -> tuple | None:
    end_lineno = getattr(node, "end_lineno", None)
    end_col = getattr(node, "end_col_offset", None)
    if end_lineno is None or end_col is None:
        return None
    return ((node.lineno - line_shift, node.col_offset - base_col),
            (end_lineno - line_shift, end_col - base_col))
def _alias_asname_span(alias_node: ast.alias, base_col: int,
                       line_shift: int) -> tuple | None:
    end_lineno = getattr(alias_node, "end_lineno", None)
    end_col = getattr(alias_node, "end_col_offset", None)
    if end_lineno is None or end_col is None:
        return None
    end_col -= base_col
    start_col = end_col - len(alias_node.asname.encode("utf-8"))
    return ((end_lineno - line_shift, start_col),
            (end_lineno - line_shift, end_col))
def _tail_binding_span(node: ast.AST, name: str, base_col: int,
                       line_shift: int) -> tuple | None:
    end_lineno = getattr(node, "end_lineno", None)
    end_col = getattr(node, "end_col_offset", None)
    if end_lineno is None or end_col is None:
        return None
    end = (end_lineno - line_shift, end_col - base_col)
    return ((end[0], end[1] - len(name.encode("utf-8"))), end)
def _token_span(line_texts: list, tok: tuple, base_col: int,
                line_shift: int) -> tuple | None:
    row, char_col, name = tok
    if not 0 < row <= len(line_texts):
        return None
    start = len(line_texts[row - 1][:char_col].encode("utf-8")) - base_col
    if start < 0:
        return None
    return ((row - line_shift, start),
            (row - line_shift, start + len(name.encode("utf-8"))))
def _def_name_token(tokens: list, node: ast.AST, keyword: str,
                    name: str) -> tuple | None:
    origin = (node.lineno, node.col_offset)
    for idx, tok in enumerate(tokens):
        if tok[:2] != origin:
            continue
        for j in range(idx, min(idx + 3, len(tokens))):
            if (tokens[j][2] == keyword and j + 1 < len(tokens)
                    and tokens[j + 1][2] == name):
                return tokens[j + 1]
        return None
    return None
def _except_name_token(tokens: list, node: ast.ExceptHandler,
                       name: str) -> tuple | None:
    start = (node.lineno, node.col_offset)
    if node.body:
        limit = (node.body[0].lineno, node.body[0].col_offset)
    else:
        limit = (getattr(node, "end_lineno", node.lineno),
                 getattr(node, "end_col_offset", node.col_offset))
    header = [tok for tok in tokens if start <= (tok[0], tok[1]) < limit]
    for prev, cur in itertools.pairwise(header):
        if prev[2] == "as" and cur[2] == name:
            return cur
    return None
def _declaration_name_tokens(tokens: list, node: ast.AST) -> list:
    start = (node.lineno, node.col_offset)
    limit = (getattr(node, "end_lineno", node.lineno),
             getattr(node, "end_col_offset", node.col_offset))
    return [tok for tok in tokens if start < (tok[0], tok[1]) < limit]
def _binding_name_token(tokens: list, node: ast.AST,
                        name: str) -> tuple | None:
    if isinstance(node, ast.ExceptHandler):
        return _except_name_token(tokens, node, name)
    if isinstance(node, DEF_NAME_TYPES):
        keyword = "class" if isinstance(node, ast.ClassDef) else "def"
        return _def_name_token(tokens, node, keyword, name)
    for tok in _declaration_name_tokens(tokens, node):
        if tok[2] == name:
            return tok
    return None
def _rest_name_token(tokens: list, node: ast.AST,
                     name: str) -> tuple | None:
    start = (node.lineno, node.col_offset)
    limit = (getattr(node, "end_lineno", node.lineno),
             getattr(node, "end_col_offset", node.col_offset))
    hits = [tok for tok in tokens
            if start <= (tok[0], tok[1]) < limit and tok[2] == name]
    return hits[-1] if hits else None
def _binding_site_spans(tree: ast.AST, valid_map: dict, text: str,
                        base_col: int, line_shift: int,
                        shadowed: dict[ast.AST, set[str]]) -> list:
    tokens = identifier_tokens(text) or ()
    line_texts = split_tokenizer_lines(text)
    spans: list = []
    for node in walk_nodes(tree):
        for name, kind in binding_sites(node):
            if (name not in valid_map
                    or name in shadowed.get(node, ())):
                continue
            if kind == "tail":
                span = _tail_binding_span(node, name, base_col, line_shift)
            elif kind == "head":
                start = (node.lineno - line_shift, node.col_offset - base_col)
                span = (start, (start[0], start[1] + len(name.encode("utf-8"))))
            else:
                tok = (_rest_name_token(tokens, node, name)
                       if kind == "rest"
                       else _binding_name_token(tokens, node, name))
                span = _token_span(line_texts, tok, base_col, line_shift) \
                    if tok is not None else None
            if span is not None:
                spans.append((*span, valid_map[name]))
    return spans
def _parameter_nodes(node: ast.AST) -> list[ast.arg]:
    args = node.args
    parameters = [*args.posonlyargs, *args.args, *args.kwonlyargs]
    parameters.extend(
        arg for arg in (args.vararg, args.kwarg) if arg is not None)
    return parameters
def _parameter_shadowed_nodes(
        tree: ast.AST, valid_map: dict,
) -> dict[ast.AST, set[str]]:
    shadowed: dict[ast.AST, set[str]] = {}
    for scope in walk_nodes(tree):
        if not isinstance(
                scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        parameters = _parameter_nodes(scope)
        names = {arg.arg for arg in parameters} & valid_map.keys()
        if not names:
            continue
        for arg in parameters:
            if arg.arg in names:
                shadowed.setdefault(arg, set()).add(arg.arg)
        body = scope.body if isinstance(scope.body, list) else [scope.body]
        for stmt in body:
            for node in walk_nodes(stmt):
                shadowed.setdefault(node, set()).update(names)
    return shadowed
def _rename_target_spans(tree: ast.AST, valid_map: dict, base_col: int,
                         line_shift: int, text: str,
                         shadowed: dict[ast.AST, set[str]]) -> list:
    spans: list = []
    for node in walk_nodes(tree):
        if isinstance(node, ast.Name):
            if (node.id in valid_map
                    and node.id not in shadowed.get(node, ())):
                span = _printed_span(node, base_col, line_shift)
                if span is not None:
                    spans.append((*span, valid_map[node.id]))
        elif isinstance(node, ast.arg):
            if (node.arg in valid_map
                    and node.arg not in shadowed.get(node, ())):
                start = (node.lineno - line_shift, node.col_offset - base_col)
                name_bytes = len(node.arg.encode("utf-8"))
                spans.append((start, (start[0], start[1] + name_bytes),
                              valid_map[node.arg]))
        elif (isinstance(node, ast.alias)
              and isinstance(node.asname, str)
              and node.asname in valid_map
              and node.asname not in shadowed.get(node, ())):
            span = _alias_asname_span(node, base_col, line_shift)
            if span is not None:
                spans.append((*span, valid_map[node.asname]))
    spans.extend(_binding_site_spans(
        tree, valid_map, text, base_col, line_shift, shadowed))
    spans.extend(_aliasless_import_rename_spans(
        tree, valid_map, base_col, line_shift, shadowed))
    return spans
def _aliasless_import_rename_spans(
        tree: ast.AST, valid_map: dict, base_col: int,
        line_shift: int, shadowed: dict[ast.AST, set[str]],
) -> list:
    spans: list = []
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for alias_node in node.names:
            if alias_node.asname is not None:
                continue
            bound = alias_node.name.split(".")[0]
            if (alias_node.name != bound or bound not in valid_map
                    or bound in shadowed.get(alias_node, ())):
                continue
            end_lineno = getattr(alias_node, "end_lineno", None)
            end_col = getattr(alias_node, "end_col_offset", None)
            if end_lineno is None or end_col is None:
                continue
            end = (end_lineno - line_shift, end_col - base_col)
            spans.append((end, end, f" as {valid_map[bound]}"))
    return spans
def _unrenamable_import_bindings(
        tree: ast.AST, valid_map: dict,
        shadowed: dict[ast.AST, set[str]],
) -> set:
    unrenamable: set = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.Import, ast.ImportFrom)):
            continue
        for alias_node in node.names:
            if alias_node.asname is not None:
                continue
            bound = alias_node.name.split(".")[0]
            if (bound not in valid_map
                    or bound in shadowed.get(alias_node, ())):
                continue
            has_span = (getattr(alias_node, "end_lineno", None) is not None
                        and getattr(alias_node, "end_col_offset", None) is not None)
            if alias_node.name == bound and has_span:
                continue
            unrenamable.add(bound)
    return unrenamable
def _apply_span_edits(text: str, spans: list) -> str:
    lines = split_tokenizer_lines(text)
    for (start_row, start_byte), (_end_row, end_byte), new_name in sorted(
            spans, key=lambda s: s[0], reverse=True):
        idx = start_row - 1
        if not 0 <= idx < len(lines):
            continue
        line_text = lines[idx]
        if not 0 <= start_byte <= end_byte <= len(line_text.encode("utf-8")):
            continue
        start_col = byte_col_to_char_col(line_text, start_byte)
        end_col = byte_col_to_char_col(line_text, end_byte)
        lines[idx] = line_text[:start_col] + new_name + line_text[end_col:]
    return "".join(lines)
def apply_variable_rename(code: str, rename_map: dict) -> str:
    code = as_text(code)
    valid_map = clean_rename_map(rename_map)
    if not valid_map:
        return code
    text = textwrap.dedent(code)
    tree, base_col, line_shift, parsed_text = parse_renameable(text)
    if tree is None:
        logger.debug("[L2] 模板代码不可解析，跳过重命名以回避按字面误改限定名")
        return code
    shadowed = _parameter_shadowed_nodes(tree, valid_map)
    blocked = _unrenamable_import_bindings(tree, valid_map, shadowed)
    if blocked:
        logger.debug("[L2] 模板名 %s 绑定于无别名 import，跳过重命名",
                     sorted(blocked))
        valid_map = {name: new for name, new in valid_map.items()
                     if name not in blocked}
        if not valid_map:
            return code
    spans = _rename_target_spans(
        tree, valid_map, base_col, line_shift, parsed_text, shadowed)
    if not spans:
        return code
    return _apply_span_edits(text, spans)
def _nested_block_ranges(func_node: ast.AST) -> list:
    ranges = []
    pending = list(ast.iter_child_nodes(func_node))
    while pending:
        child = pending.pop()
        if isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef, ast.Lambda)):
            continue
        if isinstance(child, NESTED_BLOCK_TYPES):
            start = getattr(child, 'lineno', 0)
            if start:
                ranges.append((start, getattr(child, 'end_lineno', start) or start))
        pending.extend(ast.iter_child_nodes(child))
    return ranges
def _nested_block_hit_reason(nested_ranges: list,
                             insert_line: int) -> str:
    for start, end in nested_ranges:
        if start < insert_line <= end:
            return (f"注入点(行{insert_line})位于嵌套块内 "
                    f"(行{start}-{end})，注入可能改变控制流语义")
    return ""
def ast_verify_injection_point(source: str,
                                func_name: str,
                                insert_line: int) -> tuple[bool, str]:
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("[L2] 注入点验证的源码解析降级: %s", e, exc_info=True)
        return False, "源码语法错误，无法解析AST"
    func_node = find_function_def(tree, func_name)
    if func_node is None:
        return False, f"AST中未找到函数: {func_name}"
    if function_has_inline_body(source, func_node):
        return False, "首个函数体语句与 def 签名同行，无安全行级注入点"
    nested_reason = _nested_block_hit_reason(
        _nested_block_ranges(func_node), insert_line)
    if nested_reason:
        return False, nested_reason
    func_start = func_node.lineno
    func_end = getattr(func_node, 'end_lineno', func_start)
    if not (func_start < insert_line <= func_end + 1):
        return False, (
            f"注入点(行{insert_line})不在函数范围内 "
            f"(行{func_start}-{func_end})"
        )
    return True, ""
def _template_parse_tree(template_name: str) -> ast.Module | None:
    if not isinstance(template_name, str):
        return None
    template = LOGIC_INJECTION_TEMPLATES.get(template_name, {})
    template_code = (
        template.get("code", "") if isinstance(template, dict) else "")
    return parse_template_code(template_code)
def _local_shape_names(root: ast.AST, *, name_ok=_is_local_underscore_name) -> set[str]:
    local_names: set[str] = set()
    external_names: set[str] = set()
    pending = [root]
    while pending:
        child = pending.pop()
        if child is not root and isinstance(
                child, (ast.FunctionDef, ast.AsyncFunctionDef,
                        ast.ClassDef, ast.Lambda)):
            if isinstance(child, DEF_NAME_TYPES):
                local_names.update(
                    name for name, _kind in binding_sites(child)
                    if name_ok(name))
            continue
        if isinstance(child, (ast.Global, ast.Nonlocal)):
            external_names.update(child.names)
            continue
        if isinstance(child, ast.Name):
            if (isinstance(child.ctx, (ast.Store, ast.Del))
                    and name_ok(child.id)):
                local_names.add(child.id)
        elif isinstance(child, ast.arg):
            if name_ok(child.arg):
                local_names.add(child.arg)
        elif isinstance(child, (ast.Import, ast.ImportFrom)):
            local_names.update(_import_bound_names(child, name_ok))
        else:
            local_names.update(
                name for name, _kind in binding_sites(child)
                if name_ok(name))
        pending.extend(ast.iter_child_nodes(child))
    return local_names - external_names
def _shape_dump(node: ast.AST, local_names: set[str],
                canonical_names: dict[str, str] | None = None) -> str:
    canonical = {} if canonical_names is None else canonical_names
    def _canonical_name(name: str) -> str:
        if name not in local_names:
            return name
        if name not in canonical:
            canonical[name] = f"<local:{len(canonical)}>"
        return canonical[name]
    cloned = copy.deepcopy(node)
    for child in walk_nodes(cloned):
        if isinstance(child, ast.Name):
            child.id = _canonical_name(child.id)
        elif isinstance(child, ast.arg):
            if child.arg in local_names:
                child.arg = _canonical_name(child.arg)
                child.annotation = None
        elif isinstance(child, ast.alias):
            bound = child.asname or child.name.split(".")[0]
            if bound in local_names:
                child.asname = _canonical_name(bound)
        else:
            for name, kind in binding_sites(child):
                if name not in local_names:
                    continue
                new_name = _canonical_name(name)
                if isinstance(child, (ast.Global, ast.Nonlocal)):
                    child.names = [
                        new_name if declared == name else declared
                        for declared in child.names]
                elif kind == "rest":
                    child.rest = new_name
                else:
                    child.name = new_name
    return ast.dump(cloned, include_attributes=False)
def _shape_sequence_dumps(body: list[ast.stmt],
                          local_names: set[str]) -> list[str]:
    canonical_names: dict[str, str] = {}
    return [_shape_dump(stmt, local_names, canonical_names) for stmt in body]
def _template_shape_sequence(template_tree: ast.Module) -> list[str]:
    body = list(template_tree.body)
    if (len(body) == 1
            and isinstance(body[0], (ast.FunctionDef, ast.AsyncFunctionDef))):
        body = list(body[0].body)
    local_names = _local_shape_names(ast.Module(body=body, type_ignores=[]))
    statements = [
        stmt for stmt in body
        if not (isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, str))]
    return _shape_sequence_dumps(statements, local_names)
def _iter_statement_sequences(node: ast.AST) -> Iterator[list[ast.stmt]]:
    for field in ("body", "orelse", "finalbody"):
        sequence = getattr(node, field, None)
        if not isinstance(sequence, list) or not sequence:
            continue
        yield sequence
        for stmt in sequence:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef, ast.Lambda)):
                continue
            yield from _iter_statement_sequences(stmt)
    for handler in getattr(node, "handlers", ()) or ():
        if handler.body:
            yield handler.body
            for stmt in handler.body:
                if not isinstance(stmt, (ast.FunctionDef,
                                         ast.AsyncFunctionDef,
                                         ast.ClassDef, ast.Lambda)):
                    yield from _iter_statement_sequences(stmt)
    for case in getattr(node, "cases", ()) or ():
        if case.body:
            yield case.body
            for stmt in case.body:
                if not isinstance(stmt, (ast.FunctionDef,
                                         ast.AsyncFunctionDef,
                                         ast.ClassDef, ast.Lambda)):
                    yield from _iter_statement_sequences(stmt)
def _target_contains_shape_sequence(func_node: ast.AST,
                                    shapes: list[str]) -> bool:
    if not shapes:
        return False
    width = len(shapes)
    local_names = _local_shape_names(func_node)
    for sequence in _iter_statement_sequences(func_node):
        for index in range(len(sequence) - width + 1):
            candidate = sequence[index:index + width]
            if _shape_sequence_dumps(candidate, local_names) == shapes:
                return True
    return False
def ast_check_existing_logic(source: str,
                              func_name: str,
                              template_name: str) -> bool:
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("[CodeFeedback] AST解析失败: %s", e)
        return False
    template_tree = _template_parse_tree(template_name)
    if template_tree is None:
        return False
    func_node = find_function_def(tree, func_name)
    if func_node is None:
        return False
    shapes = _template_shape_sequence(template_tree)
    if not _target_contains_shape_sequence(func_node, shapes):
        return False
    logger.info("[L2] AST检测到重复逻辑: %s (结构指纹命中 %d 条语句)",
               template_name, len(shapes))
    return True
def _iter_def_nodes(tree: ast.Module) -> Iterator[tuple[str, ast.AST]]:
    def _visit(node: ast.AST, prefix: str) -> Iterator[tuple[str, ast.AST]]:
        for child in ast.iter_child_nodes(node):
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                qualname = f"{prefix}{child.name}"
                yield qualname, child
                yield from _visit(child, f"{qualname}.")
            elif isinstance(child, ast.ClassDef):
                yield from _visit(child, f"{prefix}{child.name}.")
            else:
                yield from _visit(child, prefix)
    yield from _visit(tree, "")
def _collect_def_nodes(tree: ast.Module) -> dict[str, ast.AST]:
    return dict(_iter_def_nodes(tree))
def _collect_def_counts(tree: ast.Module) -> Counter[str]:
    return Counter(name for name, _node in _iter_def_nodes(tree))
def _collect_def_spans(nodes: dict[str, ast.AST]) -> dict[str, int]:
    return {name: getattr(node, 'end_lineno', 0) - node.lineno
            for name, node in nodes.items()}
def _direct_stmts_equivalent(orig_node: ast.AST | None,
                             mod_node: ast.AST | None) -> bool:
    def _spans(node: ast.AST) -> tuple:
        return tuple(
            getattr(stmt, 'end_lineno', stmt.lineno) - stmt.lineno
            for stmt in node.body
            if not isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef,
                                     ast.ClassDef)))
    if orig_node is None or mod_node is None:
        return False
    return _spans(orig_node) == _spans(mod_node)
def _dump_without_target_bodies(tree: ast.AST, func_name: str) -> str:
    cloned = copy.deepcopy(tree)
    nodes = _collect_def_nodes(cloned)
    for name, node in nodes.items():
        if _is_qualname_target(name, func_name):
            node.body = []
    return ast.dump(cloned, include_attributes=False)
def _target_body_insertion_only(orig_node: ast.AST | None,
                                mod_node: ast.AST | None) -> bool:
    if orig_node is None or mod_node is None:
        return False
    orig_keys = [ast.dump(stmt, include_attributes=False)
                 for stmt in orig_node.body]
    mod_keys = [ast.dump(stmt, include_attributes=False)
                for stmt in mod_node.body]
    added = len(mod_keys) - len(orig_keys)
    if added < 0:
        return False
    if added == 0:
        return orig_keys == mod_keys
    return any(
        mod_keys[:index] + mod_keys[index + added:] == orig_keys
        for index in range(len(orig_keys) + 1)
    )
def _semantic_drift_fail(orig_tree: ast.Module, mod_tree: ast.Module,
                         orig_nodes: dict[str, ast.AST],
                         mod_nodes: dict[str, ast.AST], func_name: str,
                         target_names: list[str]) -> str:
    try:
        if (_dump_without_target_bodies(orig_tree, func_name)
                != _dump_without_target_bodies(mod_tree, func_name)):
            return "非目标代码AST变化，注入影响目标函数体之外的代码"
        for name in target_names:
            if not _target_body_insertion_only(
                    orig_nodes.get(name), mod_nodes.get(name)):
                return f"目标函数 {name} 不是纯插入式变更，存在代码漂移"
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc, context='_semantic_drift_fail:PARSE_DEGRADE_EXC')
        return f"AST语义校验失败: {exc}"
    return ""
def ast_verify_diff(original_source: str,
                     modified_source: str,
                     func_name: str) -> tuple[bool, str]:
    if not isinstance(func_name, str) or not func_name:
        return False, "目标函数名非法（需非空字符串），无法验证注入落点"
    try:
        orig_tree = parse_cached(original_source)
        mod_tree = parse_cached(modified_source)
        orig_nodes = _collect_def_nodes(orig_tree)
        mod_nodes = _collect_def_nodes(mod_tree)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("[L2] AST diff 验证的源码解析降级: %s", e, exc_info=True)
        return False, f"解析失败: {e}"
    target_node = find_function_def(orig_tree, func_name)
    resolved_func_name = (
        _function_qualname(target_node, parent_map(orig_tree))
        if target_node is not None else "")
    orig_defs = _collect_def_spans(orig_nodes)
    mod_defs = _collect_def_spans(mod_nodes)
    target_names = [resolved_func_name] if resolved_func_name else []
    validators = (
        lambda: _non_target_drift_fail(
            orig_defs, mod_defs, orig_nodes, mod_nodes, resolved_func_name,
            target_names),
        lambda: _membership_drift_fail(
            orig_tree, mod_tree, resolved_func_name),
        lambda: _target_growth_fail(
            orig_defs, mod_defs, target_names, func_name),
        lambda: _semantic_drift_fail(
            orig_tree, mod_tree, orig_nodes, mod_nodes, resolved_func_name,
            target_names),
    )
    for validate in validators:
        failure = validate()
        if failure:
            return False, failure
    return True, ""
def _membership_drift_fail(orig_tree: ast.Module,
                           mod_tree: ast.Module,
                           resolved_func_name: str) -> str:
    orig_counts = _collect_def_counts(orig_tree)
    mod_counts = _collect_def_counts(mod_tree)
    def outside_target(name: str) -> bool:
        return not (resolved_func_name
                    and name.startswith(resolved_func_name + "."))
    new_defs = {name for name, count in mod_counts.items()
                if count > orig_counts[name] and outside_target(name)}
    removed_defs = {name for name, count in orig_counts.items()
                    if count > mod_counts[name] and outside_target(name)}
    if new_defs:
        return f"注入后新增函数定义: {new_defs}"
    if removed_defs:
        return f"注入后删除函数定义: {removed_defs}"
    return ""
def _is_qualname_target(name: str, resolved_name: str) -> bool:
    return name == resolved_name
def _target_growth_fail(orig_defs: dict, mod_defs: dict,
                        target_names: list, func_name: str) -> str:
    if not target_names:
        return f"目标函数 {func_name} 在原源码中不存在，无法验证注入落点"
    if not any(mod_defs.get(n, 0) > orig_defs[n] for n in target_names):
        first = target_names[0]
        return (f"目标函数 {func_name} 行数未增加 "
                f"(原:{orig_defs[first]} -> 改:{mod_defs.get(first, 0)})，注入可能失败")
    return ""
def _exempt_prefix_chain(target_names: list, orig_defs: dict,
                         mod_defs: dict) -> set:
    exempt: set[str] = set()
    for n in target_names:
        if mod_defs.get(n, 0) > orig_defs[n]:
            parts = n.split(".")
            exempt.update(".".join(parts[:i]) for i in range(1, len(parts)))
    return exempt
def _non_target_drift_fail(orig_defs: dict, mod_defs: dict,
                           orig_nodes: dict, mod_nodes: dict,
                           func_name: str, target_names: list) -> str:
    exempt = _exempt_prefix_chain(target_names, orig_defs, mod_defs)
    for name, orig_lines in orig_defs.items():
        if _is_qualname_target(name, func_name):
            continue
        mod_lines = mod_defs.get(name, 0)
        if mod_lines == orig_lines:
            continue
        if name in exempt and _direct_stmts_equivalent(
                orig_nodes.get(name), mod_nodes.get(name)):
            continue
        return (f"非目标函数 {name} 行数变化 "
                f"(原:{orig_lines} -> 改:{mod_lines})，注入影响其他函数")
    return ""
@dataclass(frozen=True, slots=True)
class _InjectionPlan:
    file_path: str
    eol: str
    bom_prefix: str
    modified_content: str
    original_content: str
    template_name: str
    insert_line: int
    diff_preview: str
    encoding: str = "utf-8"
def _coerce_confidence(value: object) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return DEFAULT_CONFIDENCE_FALLBACK
    try:
        number = float(value)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context='_coerce_confidence:coerce')
        return DEFAULT_CONFIDENCE_FALLBACK
    if not math.isfinite(number):
        return DEFAULT_CONFIDENCE_FALLBACK
    return min(1.0, max(0.0, number))
@dataclass(frozen=True, slots=True)
class ModRef:
    mod_id: str
    target_file: str
    target_function: str = ""
    confidence: float = DEFAULT_CONFIDENCE_FALLBACK
    source_enhancement_id: str = _DEFAULT_SOURCE_ENHANCEMENT_ID
    @property
    def target_name(self) -> str:
        if self.target_function:
            return f"{self.target_file}::{self.target_function}"
        return self.target_file
def _fail_record(ref: ModRef, action_type: str, error_message: str,
                 **audit: Any) -> FeedbackModification:
    is_injection = action_type == "logic_inject"
    log_label = "逻辑注入失败" if is_injection else "源码修复失败"
    log_target = ref.target_name if is_injection else ref.target_file
    kwargs: dict[str, Any] = {
        "modification_id": ref.mod_id, "level": "L2",
        "target_file": ref.target_file, "target_name": ref.target_name,
        "action_type": action_type, "applied": False,
        "confidence": ref.confidence, "error_message": error_message,
        "source_enhancement_id": ref.source_enhancement_id,
    }
    kwargs.update(audit)
    logger.warning("[L2] %s %s: %s → %s",
                   log_label, ref.mod_id, error_message, log_target)
    return FeedbackModification(**kwargs)
def _injection_record(ref: ModRef, template_name: str, insert_line: int,
                     diff_preview: str, backup_path: str) -> FeedbackModification:
    return FeedbackModification(
        modification_id=ref.mod_id, level="L2",
        target_file=ref.target_file,
        target_name=ref.target_name,
        action_type="logic_inject",
        original_value=f"inject at line {insert_line + 1}",
        new_value=f"template: {template_name}",
        diff_preview=diff_preview,
        syntax_valid=True,
        backup_path=backup_path,
        applied=True,
        timestamp=time.strftime(FMT_DATETIME),
        confidence=ref.confidence,
        source_enhancement_id=ref.source_enhancement_id,
    )
def _normalize_newlines(text: str) -> str:
    return text.replace(_CRLF, _LF).replace("\r", _LF)
def _apply_newline(text: str, newline: str) -> str:
    return text.replace(_LF, newline) if newline and newline != _LF else text
def _read_source_text(file_path: str, tag: str) -> tuple[str | None, str, str]:
    try:
        with open(file_path, "rb") as f:
            raw = f.read()
        text, encoding = decode_source_strict(raw)
    except (OSError, UnicodeDecodeError, LookupError, ValueError) as e:
        logger.debug("[%s] 源文件按声明编码读取失败: %s", tag, e, exc_info=True)
        return None, "utf-8", str(e)
    if raw.startswith(codecs.BOM_UTF8):
        text = raw.decode("utf-8")
        encoding = "utf-8"
    return text, encoding, ""
def _template_code_for_encoding(code: str, encoding: str) -> str:
    try:
        code.encode(encoding)
    except UnicodeEncodeError:
        pass
    else:
        return code
    escaped = code.encode(
        encoding, errors="backslashreplace").decode(encoding)
    original_tree = parse_template_code(code)
    escaped_tree = parse_template_code(escaped)
    if (original_tree is not None and escaped_tree is not None
            and ast.dump(original_tree, include_attributes=False)
            == ast.dump(escaped_tree, include_attributes=False)):
        return escaped
    return code
def _declared_source_encoding(source: str) -> str:
    encoding, _lines = tokenize.detect_encoding(
        io.BytesIO(source.encode("utf-8")).readline)
    return codecs.lookup(encoding or "utf-8").name
def _source_encoding_drift(original: str, modified: str) -> str:
    try:
        original_encoding = _declared_source_encoding(original)
        modified_encoding = _declared_source_encoding(modified)
    except (SyntaxError, UnicodeError, LookupError, ValueError) as e:
        return f"源码编码声明无法解析，已拒绝写盘: {e}"
    if original_encoding != modified_encoding:
        return (
            f"源码编码声明变化（{original_encoding} -> {modified_encoding}），"
            "与保持原编码写盘不兼容；请先单独完成编码迁移，避免写后乱码")
    return ""
def _resolve_target_path(skill_dir: str, target_file: str) -> str:
    if not isinstance(target_file, str) or not target_file.strip():
        return ""
    try:
        if os.path.isabs(target_file) or os.path.splitdrive(target_file)[0]:
            return ""
    except (TypeError, ValueError) as _e:
        log_swallowed(__name__, _e, context='_resolve_target_path:path')
        return ""
    return resolve_within_root(skill_dir, target_file) or ""
_MOD_SEQ = itertools.count(1)
def _next_mod_id(prefix: str = "") -> str:
    return f"MOD-L2{prefix}-{int(time.time() * 1000)}-{next(_MOD_SEQ):04d}"
def _write_with_backup(file_path: str, content: str, skill_dir: str,
                       tag: str, log_tag: str,
                       encoding: str) -> tuple[str, str]:
    try:
        backup_path = archive_backup(file_path, skill_dir, tag)
    except (OSError, RuntimeError, ValueError) as e:
        logger.warning("[%s] 备份归口不可用，拒绝无备份修改: %s", tag, e)
        backup_path = ""
    if not backup_path:
        return f"备份失败，磁盘未修改: {file_path}", ""
    write_err = write_with_rollback(
        file_path, content, backup_path, tag, log_tag, encoding=encoding)
    return write_err, backup_path
@dataclass(frozen=True)
class L2InjectionPlan:
    template_name: str = ""
    target_file: str = ""
    target_function: str = ""
    skip_reason: str = ""
def _entry_dict(entry: object) -> dict:
    return dict(entry) if isinstance(entry, Mapping) else {}
def resolve_injection_target(
        entry: object,
        aliases: Mapping[str, str | None] | None = None,
) -> tuple[str, str]:
    entry_dict = _entry_dict(entry)
    return parse_injection_target(
        str_field(entry_dict, "target"), entry_dict, aliases)
def plan_l2_injection(
        entry: object,
        aliases: Mapping[str, str | None] | None = None,
) -> L2InjectionPlan:
    entry_dict = _entry_dict(entry)
    template_name = match_l2_template(
        str_field(entry_dict, "description").lower(), entry_dict)
    target_file, target_function = resolve_injection_target(entry_dict, aliases)
    if not target_file or not target_function:
        return L2InjectionPlan(
            template_name=template_name, target_file=target_file,
            skip_reason=f"无法解析注入目标: {str_field(entry_dict, 'target')}")
    return L2InjectionPlan(template_name, target_file, target_function)
class LogicInjector:
    def __init__(self, skill_dir: str):
        root = coerce_target_file(skill_dir)
        self.skill_dir = normalize_skill_dir(root) if root else ""
        self._injection_marker = "[auto-injected"
    def _inject_rollback_fail(self, file_path: str, backup: str,
                              ref: ModRef, cause: str,
                              **audit: Any) -> FeedbackModification:
        return _fail_record(
            ref, "logic_inject",
            f"{cause}{rollback_note(file_path, backup, '[L2] inject')}",
            **audit)
    def _post_write_syntax_fail(self, file_path: str, backup_path: str,
                                ref: ModRef) -> FeedbackModification | None:
        ok, err = self._syntax_gate(file_path)
        if ok:
            return None
        logger.error("[L2] 写后语法验证失败 %s: %s", file_path, err)
        return self._inject_rollback_fail(
            file_path, backup_path, ref, "语法验证失败",
            syntax_valid=False, backup_path=backup_path)
    def _post_write_diff_fail(self, file_path: str, backup_path: str,
                              ref: ModRef,
                              original_content: str,
                              encoding: str) -> FeedbackModification | None:
        try:
            with open(file_path, encoding=encoding, newline="") as f:
                modified_source = strip_bom(f.read())
        except (OSError, UnicodeDecodeError) as e:
            logger.debug(
                "[L2:_post_write_diff_fail] (OSError, UnicodeDecodeError) 降级路径: %s",
                e, exc_info=True)
            return self._inject_rollback_fail(
                file_path, backup_path, ref, f"验证读回失败: {e}",
                syntax_valid=False, backup_path=backup_path)
        diff_safe, diff_reason = ast_verify_diff(
            original_content, modified_source, ref.target_function)
        if diff_safe:
            return None
        return self._inject_rollback_fail(
            file_path, backup_path, ref, f"AST diff验证失败: {diff_reason}",
            syntax_valid=True, backup_path=backup_path)
    def _inject_verify_and_rollback(
        self, file_path: str, backup_path: str, ref: ModRef,
        original_content: str, encoding: str,
    ) -> FeedbackModification | None:
        syntax_fail = self._post_write_syntax_fail(file_path, backup_path, ref)
        if syntax_fail is not None:
            return syntax_fail
        return self._post_write_diff_fail(
            file_path, backup_path, ref, original_content, encoding)
    def _preflight_template(self, ref: ModRef, template_name: str) -> tuple:
        if not _template_name_ok(template_name):
            return _fail_record(
                ref, "logic_inject",
                "注入模板名非法（需非空字符串且不含换行/控制字符）: "
                f"{type(template_name).__name__}"), ""
        template = LOGIC_INJECTION_TEMPLATES.get(template_name)
        if not template:
            return _fail_record(
                ref, "logic_inject", f"未知注入模板: {template_name}"), ""
        if not isinstance(template, dict):
            return _fail_record(
                ref, "logic_inject", f"模板 {template_name} 结构不合规"
                     f"（注册表条目为 {type(template).__name__}），跳过注入"), ""
        template_code = template.get("code")
        if not isinstance(template_code, str) or not template_code.strip():
            return _fail_record(
                ref, "logic_inject", f"模板 {template_name} 结构不合规"
                     "（code 缺失/非字符串/为空），跳过注入"), ""
        if not _code_syntax_ok(template_name, template_code):
            return _fail_record(
                ref, "logic_inject",
                f"模板 {template_name} 未通过函数体语法/控制流校验，跳过注入"), ""
        _inject_point = template.get("inject_point")
        if _inject_point != DEFAULT_INJECT_POINT:
            return _fail_record(
                ref, "logic_inject",
                (f"模板 {template_name} 的注入点 {_inject_point!r} 不受支持"
                 f"（执行器只实现 {DEFAULT_INJECT_POINT}），跳过注入")), ""
        if is_template_disabled(template_name, self.skill_dir):
            return _fail_record(
                ref, "logic_inject", (f"模板 {template_name} 已因连续失败 "
                      f"{TEMPLATE_FAILURE_THRESHOLD} 次被熔断，跳过注入")), ""
        return None, template_code
    @staticmethod
    def _load_normalized_source(file_path: str, ref: ModRef) -> tuple:
        if not os.path.isfile(file_path):
            return _fail_record(
                ref, "logic_inject", f"文件不存在: {file_path}"), "", _LF, "", "utf-8"
        original_content, encoding, read_err = _read_source_text(
            file_path, "L2:inject")
        if original_content is None:
            return _fail_record(
                ref, "logic_inject", f"文件读取失败: {read_err}"), "", _LF, "", "utf-8"
        eol = detect_newline(original_content)
        original_content = _normalize_newlines(original_content)
        bom_prefix = "\ufeff" if original_content.startswith("\ufeff") else ""
        return (None, strip_bom(original_content), eol, bom_prefix, encoding)
    @staticmethod
    def _marker_applies_to_target(source: str, func_name: str,
                                  marker_line: int) -> bool:
        try:
            tree = parse_cached(source)
        except PARSE_DEGRADE_EXC:  # jwsgj:silent-ok 纯值降级：入参不可解析时返回安全默认值，无副作用可留痕
            return True
        target = find_function_def(tree, func_name)
        if target is None:
            return True
        functions = [
            node for node in walk_nodes(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        owners = [
            node for node in functions
            if node.lineno <= marker_line <= (
                getattr(node, "end_lineno", node.lineno) or node.lineno)
        ]
        if not owners:
            return True
        owner = min(
            owners,
            key=lambda node: (
                (getattr(node, "end_lineno", node.lineno) or node.lineno)
                - node.lineno,
                -node.lineno,
            ),
        )
        return owner is target
    def _dup_injection_fail(self, original_content: str, ref: ModRef,
                            template_name: str) -> FeedbackModification | None:
        if ast_check_existing_logic(
                original_content, ref.target_function, template_name):
            return _fail_record(
                ref, "logic_inject",
                f"AST检测到相似逻辑已存在于 {ref.target_function}，跳过注入")
        current_marker = f"{self._injection_marker}: {template_name}]"
        legacy_marker = f"{self._injection_marker}]"
        marker_pattern = re.compile(
            rf"(?:{re.escape(current_marker)}|"
            rf"(?=.*{re.escape(legacy_marker)}).*\b{re.escape(template_name)}\b)")
        try:
            comment_lines = [
                (token.start[0], token.string)
                for token in tokenize.generate_tokens(
                    iter(split_tokenizer_lines(original_content)).__next__)
                if token.type == tokenize.COMMENT
            ]
        except (tokenize.TokenError, *PARSE_DEGRADE_EXC) as e:
            logger.debug("[L2] 重复标记注释扫描失败，交由注入点解析门禁处理: %s", e)
            return None
        if any(marker_pattern.search(line)
               and self._marker_applies_to_target(
                   original_content, ref.target_function, line_no)
               for line_no, line in comment_lines):
            return _fail_record(
                ref, "logic_inject",
                f"模板 {template_name} 已存在于目标函数或文件级标记中，跳过重复注入")
        return None
    def _compose_injection(self, original_content: str, ref: ModRef,
                           template_name: str, template_code: str,
                           encoding: str) -> tuple:
        target_function = ref.target_function
        insert_line = find_function_end(original_content, target_function)
        if insert_line is None:
            return _fail_record(
                ref, "logic_inject",
                f"未找到函数或无安全函数尾注入点: {target_function}"), [], [], 0
        is_safe, reason = ast_verify_injection_point(
            original_content, target_function, insert_line + 1)
        if not is_safe:
            return _fail_record(
                ref, "logic_inject", f"注入点不安全: {reason}"), [], [], 0
        template_code_raw = _template_code_for_encoding(
            f"    # [auto-injected: {template_name}]\n"
            + _wrap_template_scope(template_code), encoding)
        has_conflict, rename_map = detect_variable_conflicts(
            original_content, target_function, template_code_raw)
        if has_conflict and not rename_map:
            return _fail_record(
                ref, "logic_inject",
                "模板自由变量与目标局部/闭包绑定冲突，无法安全消歧，拒绝注入"
            ), [], [], 0
        if has_conflict:
            template_code_raw = apply_variable_rename(
                template_code_raw, rename_map)
            residual_conflict, residual_names = detect_variable_conflicts(
                original_content, target_function, template_code_raw)
            if residual_conflict:
                unresolved = ", ".join(sorted(residual_names))
                detail = (f"模板变量冲突无法安全消歧: {unresolved}"
                          if unresolved else
                          "模板自由变量与目标局部/闭包绑定冲突")
                return _fail_record(
                    ref, "logic_inject", f"{detail}，拒绝注入"
                ), [], [], 0
        inject_code = indent_code(
            template_code_raw, target_function, original_content)
        lines = split_tokenizer_lines(original_content)
        if insert_line > 0 and not lines[insert_line - 1].endswith(("\n", "\r")):
            lines[insert_line - 1] += "\n"
        modified_lines = [*lines[:insert_line], inject_code, *lines[insert_line:]]
        return None, lines, modified_lines, insert_line
    def _write_injection(self, plan: _InjectionPlan, ref: ModRef) -> tuple:
        write_err, backup_path = _write_with_backup(
            plan.file_path,
            _apply_newline(plan.bom_prefix + plan.modified_content, plan.eol),
            self.skill_dir, "L2", "[L2] inject",
            encoding=plan.encoding)
        if write_err:
            record_template_application(
                plan.template_name, False, self.skill_dir)
            return _fail_record(
                ref, "logic_inject", write_err,
                original_value=f"inject at line {plan.insert_line + 1}",
                new_value=f"template: {plan.template_name}",
                diff_preview=plan.diff_preview, backup_path=backup_path), backup_path
        verify_err = self._inject_verify_and_rollback(
            plan.file_path, backup_path, ref, plan.original_content,
            plan.encoding)
        if verify_err is not None:
            record_template_application(
                plan.template_name, False, self.skill_dir)
            return verify_err, backup_path
        record_template_application(plan.template_name, True, self.skill_dir)
        return None, backup_path
    def inject(self, target_file: str, target_function: str,
               template_name: str,
               source_enhancement_id: str = _DEFAULT_SOURCE_ENHANCEMENT_ID,
               confidence: float = DEFAULT_CONFIDENCE_FALLBACK) -> FeedbackModification:
        target_file = coerce_target_file(target_file)
        target_function = as_text(target_function).strip()
        ref = ModRef(_next_mod_id(), target_file, target_function,
                      _coerce_confidence(confidence), source_enhancement_id)
        if not self.skill_dir:
            return _fail_record(ref, "logic_inject", "技能根为空或非法，拒绝注入")
        if not target_file:
            return _fail_record(ref, "logic_inject", "目标文件路径非法或空白，跳过注入")
        fail_mod, template_code = self._preflight_template(ref, template_name)
        if fail_mod is not None:
            return fail_mod
        file_path = _resolve_target_path(self.skill_dir, target_file)
        if not file_path:
            return _fail_record(
                ref, "logic_inject",
                f"目标文件路径越界（必须在技能根内）: {target_file}")
        fail_mod, original_content, eol, bom_prefix, encoding = (
            self._load_normalized_source(file_path, ref))
        if fail_mod is not None:
            return fail_mod
        fail_mod = self._dup_injection_fail(
            original_content, ref, template_name)
        if fail_mod is not None:
            return fail_mod
        fail_mod, lines, modified_lines, insert_line = self._compose_injection(
            original_content, ref, template_name, template_code, encoding)
        if fail_mod is not None:
            return fail_mod
        modified_content = "".join(modified_lines)
        diff_preview = format_diff_preview(
            lines, modified_lines, target_file)
        fail_mod, backup_path = self._write_injection(
            _InjectionPlan(file_path, eol, bom_prefix, modified_content,
                           original_content, template_name, insert_line,
                           diff_preview, encoding),
            ref)
        if fail_mod is not None:
            return fail_mod
        logger.info(
            "[L2] 逻辑注入成功: %s::%s, template=%s",
            target_file, target_function, template_name,
        )
        return _injection_record(
            ref, template_name, insert_line, diff_preview, backup_path)
    def _syntax_gate(self, file_path: str) -> tuple[bool, str]:
        try:
            with open(file_path, "rb") as f:
                source = f.read()
        except OSError as e:
            logger.debug("[L2:_syntax_gate] OSError 降级路径: %s", e, exc_info=True)
            return False, f"OSError: {e}"
        compile_err = compile_error(source, file_path, "_syntax_gate")
        return (not compile_err), compile_err
def _source_fix_success(ref: ModRef, backup_path: str,
                        original_value: str, new_value: str) -> FeedbackModification:
    return FeedbackModification(
        modification_id=ref.mod_id, level="L2",
        target_file=ref.target_file, target_name=ref.target_name,
        action_type="source_fix", applied=True, syntax_valid=True,
        confidence=ref.confidence,
        source_enhancement_id=ref.source_enhancement_id,
        backup_path=backup_path,
        original_value=original_value, new_value=new_value,
        timestamp=time.strftime(FMT_DATETIME),
    )
def _normalize_fix_spec(spec: Any) -> tuple[str | None, str | None]:
    if not isinstance(spec, Mapping):
        logger.warning("[SourceFix] fix_specs 含非对象元素(%s)，跳过该条",
                       type(spec).__name__)
        return None, None
    find = spec.get("find")
    replace = spec.get("replace")
    if not isinstance(find, str):
        if find:
            logger.warning(
                "[SourceFix] fix 条目 find 非 str(%s)，跳过该条",
                type(find).__name__)
        return None, None
    if replace is None:
        replace = ""
    elif not isinstance(replace, str):
        logger.warning(
            "[SourceFix] fix 条目 replace 非 str(%s)，跳过该条",
            type(replace).__name__)
        return None, None
    find = _normalize_newlines(find)
    replace = _normalize_newlines(replace)
    if not find:
        return None, None
    return find, replace
def _apply_fix_specs(
        content: str, fix_specs: list) -> tuple[str, int, list, int, list]:
    changed = 0
    rejected = 0
    applied_specs: list[tuple[str, str]] = []
    missing: list[str] = []
    for spec in fix_specs or []:
        find, replace = _normalize_fix_spec(spec)
        if find is None:
            rejected += 1
            continue
        if find not in content:
            missing.append(find)
            continue
        updated = content.replace(find, replace, 1)
        if updated == content:
            continue
        content = updated
        changed += 1
        applied_specs.append((find, replace))
    return content, changed, applied_specs, rejected, missing
class SourceFixApplier:
    def __init__(self, skill_dir: str) -> None:
        root = coerce_target_file(skill_dir)
        self.skill_dir = normalize_skill_dir(root) if root else ""
    def _read_original(self, full_path: str, ref: ModRef) -> tuple:
        content, encoding, read_err = _read_source_text(
            full_path, "SourceFix")
        if content is None:
            return _fail_record(
                ref, "source_fix", f"读取失败: {read_err}"), "", "utf-8"
        return None, content, encoding
    def _preflight_apply(self, full_path: str, ref: ModRef) -> tuple:
        if not os.path.isfile(full_path):
            return _fail_record(
                ref, "source_fix",
                f"目标文件不存在: {ref.target_file}"), "", _LF, "utf-8"
        fail_mod, original, encoding = self._read_original(full_path, ref)
        if fail_mod is not None:
            return fail_mod, "", _LF, "utf-8"
        return None, original, detect_newline(original), encoding
    def _apply_specs_gates(self, original: str, fix_specs: list | tuple,
                           newline: str, ref: ModRef) -> tuple:
        if fix_specs is None:
            fix_specs = []
        if not isinstance(fix_specs, (list, tuple)):
            return (_fail_record(
                ref, "source_fix", f"fix_specs 类型非法（需 list/tuple，收到 "
                     f"{type(fix_specs).__name__}），未应用任何修改"),
                "", "", "")
        content = _normalize_newlines(original)
        content, changed, applied_specs, rejected, missing = _apply_fix_specs(
            content, fix_specs)
        if rejected:
            logger.warning(
                "[SourceFix] fix_specs 含 %d 条非法规格，拒绝整批修改",
                rejected)
            return (_fail_record(
                ref, "source_fix",
                f"fix_specs 含 {rejected} 条非法规格，已拒绝整批修改"),
                "", "", "")
        if missing:
            preview = _LF.join(missing)[:200]
            logger.warning(
                "[SourceFix] fix_specs 未命中(%d 条)，拒绝整批修改",
                len(missing))
            return (_fail_record(
                ref, "source_fix", f"fix_specs 含 {len(missing)} 条未命中（find 在目标"
                     f"文件中不存在），已拒绝整批修改: {preview}"),
                "", "", "")
        if changed == 0:
            return (_fail_record(
                ref, "source_fix", "已修复或无需修改(幂等)"), "", "", "")
        applied_finds = (_LF.join(s[0] for s in applied_specs))[:200]
        applied_replaces = (_LF.join(s[1] for s in applied_specs))[:200]
        compile_err = compile_error(
            _apply_newline(strip_bom(content), newline),
            ref.target_file, "apply")
        if compile_err:
            return (_fail_record(
                ref, "source_fix", f"语法验证失败，未写入: {compile_err}",
                syntax_valid=False,
                original_value=applied_finds),
                "", applied_finds, "")
        comment_fail = self._full_source_gates(original, content, ref)
        if comment_fail is not None:
            return comment_fail, "", applied_finds, ""
        return None, content, applied_finds, applied_replaces
    def _write_and_rollback(self, full_path: str, original_content: str,
                            write_content: str, ref: ModRef, tag: str,
                            log_tag: str, encoding: str) -> tuple:
        encoding_drift = _source_encoding_drift(original_content, write_content)
        if encoding_drift:
            return _fail_record(ref, "source_fix", encoding_drift), ""
        write_err, backup_path = _write_with_backup(
            full_path, write_content, self.skill_dir, tag, log_tag,
            encoding=encoding)
        if write_err:
            return _fail_record(
                ref, "source_fix", write_err, backup_path=backup_path), backup_path
        return None, backup_path
    def _prepare_source_fix(self, target_file: str,
                            source_enhancement_id: str,
                            confidence: float) -> tuple:
        target_file = coerce_target_file(target_file)
        ref = ModRef(_next_mod_id("-SRC"), target_file,
                     confidence=_coerce_confidence(confidence),
                     source_enhancement_id=source_enhancement_id)
        if not self.skill_dir:
            return ref, "", _fail_record(
                ref, "source_fix", "技能根为空或非法，拒绝修改")
        if not target_file:
            return ref, "", _fail_record(
                ref, "source_fix", "目标文件路径非法或空白，跳过")
        full_real = _resolve_target_path(self.skill_dir, target_file)
        if not full_real:
            logger.warning("[L2:apply] 目标越界拒绝(不在技能根内): %s",
                           target_file)
            return ref, "", _fail_record(
                ref, "source_fix", f"目标文件越界（不在技能根内）: {target_file}")
        return ref, full_real, None
    def apply(self, target_file: str, fix_specs: list,
              source_enhancement_id: str = _DEFAULT_SOURCE_ENHANCEMENT_ID,
              confidence: float = DEFAULT_CONFIDENCE_FALLBACK) -> FeedbackModification:
        ref, full_path, fail_mod = self._prepare_source_fix(
            target_file, source_enhancement_id, confidence)
        if fail_mod is not None:
            return fail_mod
        fail_mod, original, newline, encoding = self._preflight_apply(
            full_path, ref)
        if fail_mod is not None:
            return fail_mod
        fail_mod, content, applied_finds, applied_replaces = (
            self._apply_specs_gates(original, fix_specs, newline, ref))
        if fail_mod is not None:
            return fail_mod
        fail_mod, backup_path = self._write_and_rollback(
            full_path, original, _apply_newline(content, newline), ref,
            "srcfix", "[SourceFix] apply", encoding)
        if fail_mod is not None:
            return fail_mod
        return _source_fix_success(
            ref, backup_path, applied_finds, applied_replaces)
    def _preflight_full_source(self, fixed_source: str, full_path: str,
                               ref: ModRef) -> tuple:
        if not isinstance(fixed_source, str) or not fixed_source.strip():
            return (_fail_record(
                ref, "source_fix", f"fixed_source 为空或类型非法（需 str，收到 "
                     f"{type(fixed_source).__name__}）"), "", "utf-8")
        if not os.path.isfile(full_path):
            return (_fail_record(
                ref, "source_fix", f"目标文件不存在: {ref.target_file}"), "", "utf-8")
        compile_err = compile_error(
            strip_bom(fixed_source), ref.target_file, "_preflight_full_source")
        if compile_err:
            return (_fail_record(
                ref, "source_fix", f"修复源码语法错误: {compile_err}",
                syntax_valid=False), "", "utf-8")
        return self._read_original(full_path, ref)
    def _full_source_gates(self, original: str, fixed_source: str,
                           ref: ModRef) -> FeedbackModification | None:
        if (_normalize_newlines(strip_bom(original))
                == _normalize_newlines(strip_bom(fixed_source))):
            return _fail_record(ref, "source_fix", "内容无变化(幂等)")
        _comment_issues = check_comment_docstring_sync(
            original, strip_bom(fixed_source), ref.target_file)
        if not _comment_issues:
            return None
        _cm_detail = "；".join(
            f"[{i['kind']}] {i['detail']}" for i in _comment_issues[:3])
        logger.debug(
            "[L2:_full_source_gates] 注释/docstring 未同步拒绝写盘: %s",
            _cm_detail)
        return _fail_record(
            ref, "source_fix",
            f"注释/docstring 未同步（fix_scope.comments 写盘门禁）: "
            f"{_cm_detail}。修复改变行为/语义/契约时须同步更新相关"
            f"docstring 与注释，请同步修订后重新提交")
    def _write_full_source(self, full_path: str, original: str,
                           fixed_source: str, ref: ModRef,
                           encoding: str) -> tuple:
        bom_prefix = "\ufeff" if original.startswith("\ufeff") else ""
        newline = detect_newline(original)
        content = _normalize_newlines(strip_bom(fixed_source))
        write_content = _apply_newline(bom_prefix + content, newline)
        compile_err = compile_error(
            strip_bom(write_content), ref.target_file, "_write_full_source")
        if compile_err:
            return _fail_record(
                ref, "source_fix", f"语法验证失败，未写入: {compile_err}",
                syntax_valid=False), ""
        return self._write_and_rollback(
            full_path, original, write_content, ref,
            "srcfix-full", "[SourceFix] apply_full_source", encoding)
    def apply_full_source(self, target_file: str, fixed_source: str,
                          source_enhancement_id: str = _DEFAULT_SOURCE_ENHANCEMENT_ID,
                          confidence: float = DEFAULT_CONFIDENCE_FALLBACK) -> FeedbackModification:
        ref, full_path, fail_mod = self._prepare_source_fix(
            target_file, source_enhancement_id, confidence)
        if fail_mod is not None:
            return fail_mod
        fail_mod, original, encoding = self._preflight_full_source(
            fixed_source, full_path, ref)
        if fail_mod is not None:
            return fail_mod
        fail_mod = self._full_source_gates(original, fixed_source, ref)
        if fail_mod is not None:
            return fail_mod
        fail_mod, backup_path = self._write_full_source(
            full_path, original, fixed_source, ref, encoding)
        if fail_mod is not None:
            return fail_mod
        return _source_fix_success(
            ref, backup_path, "full source replace",
            f"AI 审核源码全文替换 ({len(fixed_source)} chars) 已应用")
__all__ = [
    'DEF_NAME_TYPES',
    'LOGIC_INJECTION_TEMPLATES',
    'NESTED_BLOCK_TYPES',
    'TEMPLATE_FAILURE_THRESHOLD',
    'LogicInjector',
    'SourceFixApplier',
    'as_text',
    'binding_sites',
    'clean_rename_map',
    'detect_variable_conflicts',
    'find_function_def',
    'find_function_end',
    'function_has_inline_body',
    'get_template_stats',
    'indent_code',
    'is_template_disabled',
    'match_l2_template',
    'parse_injection_target',
    'parse_renameable',
    'parse_template_code',
    'plan_l2_injection',
    'record_template_application',
    'register_injection_template',
    'resolve_injection_target',
    'underscore_mentions',
]

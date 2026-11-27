# ruff: noqa: I001
from __future__ import annotations
import ast
import hashlib
import io
import json
import keyword
import logging
import math
import os
import re
import threading
import tokenize
from collections.abc import Mapping
from dataclasses import dataclass, field
from typing import Any
try:
    import tomllib
except ModuleNotFoundError:
    import tomli as tomllib
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
__all__ = [
    "CODE_LANGUAGES",
    "ENTRYPOINT_STEMS",
    "LANGUAGE_BY_SUFFIX",
    "LAYOUT_DOC",
    "LAYOUT_EMPTY",
    "LAYOUT_FLAT",
    "LAYOUT_OTHER",
    "LAYOUT_SCRIPTS",
    "LAYOUT_SRC",
    "LEGACY_DECLARATION_MODULE",
    "PROFILE_FILENAME",
    "PROFILE_SCHEMA",
    "SELF_PRIVILEGE_PATTERNS",
    "SOURCE_DIR_NAMES",
    "SkillLayout",
    "SkillProfile",
    "SkillProfileError",
    "audit_language_assumption",
    "audit_self_privilege",
    "detect_layout",
    "is_appledouble_basename",
    "is_scan_py_name",
    "is_self_skill",
    "is_temp_artifact_dir",
    "is_test_source_name",
    "load_declared_profile",
    "profile_diagnostics",
    "python_import_roots",
    "reset_profile_cache",
    "resolve_skill_profile",
    "self_skill_root",
]
_log = logging.getLogger(__name__)
_PARSE_DEGRADE_EXC = (
    SyntaxError, ValueError, TypeError, RecursionError, MemoryError)
PROFILE_FILENAME = "skill_profile.json"
PROFILE_SCHEMA = "skill-profile/1"
LEGACY_DECLARATION_MODULE = "diag_module_topology.py"
_DEFAULT_PROFILE_SOURCE = "derived"
_DEFAULT_STRICT = False
_DEFAULT_INCLUDE_DEBT = False
_SELF_ROOT = os.path.realpath(os.path.dirname(os.path.abspath(__file__)))
_PROFILE_CACHE: dict[str, tuple[tuple[Any, ...], SkillProfile]] = {}
_PROFILE_LOCK = threading.Lock()
class SkillProfileError(ValueError):
    pass
def _as_str_tuple(value: Any) -> tuple[str, ...]:
    if isinstance(value, (str, bytes)) or not isinstance(value, (list, tuple, set, frozenset)):
        return ()
    if isinstance(value, (set, frozenset)):
        if not all(isinstance(item, str) for item in value):
            return ()
        value = sorted(value)
    items = []
    for item in value:
        if not isinstance(item, str) or not item:
            return ()
        if item not in items:
            items.append(item)
    return tuple(items)
def _text_field(value: Any) -> str:
    return value.strip() if isinstance(value, str) else ""
def _as_str_map(value: Any) -> dict[str, str]:
    if not isinstance(value, dict):
        return {}
    return {
        key.strip(): val.strip()
        for key, val in value.items()
        if isinstance(key, str) and key.strip()
        and isinstance(val, str) and val.strip()
    }
_DEFAULT_PREFIX_CONFIDENCE = 0.8
def _finite_number(value: Any) -> float | None:
    if isinstance(value, bool):
        return None
    if isinstance(value, (int, float)):
        try:
            number = float(value)
        except OverflowError as exc:
            log_swallowed(
                __name__, exc, context=f"_finite_number:{type(exc).__name__}")
            return None
    elif isinstance(value, str):
        try:
            number = float(value.strip())
        except ValueError:
            return None
    else:
        return None
    return number if math.isfinite(number) else None
def _confidence_value(value: Any) -> float:
    number = _finite_number(value)
    if number is None:
        return _DEFAULT_PREFIX_CONFIDENCE
    return min(1.0, max(0.0, number))
def _as_prefix_map(value: Any) -> dict[str, tuple[str, str, float]]:
    if not isinstance(value, dict):
        return {}
    parsed: dict[str, tuple[str, str, float]] = {}
    for raw_prefix, spec in value.items():
        if not isinstance(raw_prefix, str):
            continue
        prefix = raw_prefix.strip()
        if not prefix:
            continue
        domain = sub_domain = ""
        confidence = _DEFAULT_PREFIX_CONFIDENCE
        if isinstance(spec, (list, tuple)) and len(spec) >= 2:
            domain = spec[0].strip() if isinstance(spec[0], str) else ""
            sub_domain = spec[1].strip() if isinstance(spec[1], str) else ""
            if len(spec) >= 3:
                confidence = _confidence_value(spec[2])
        elif isinstance(spec, dict):
            domain = _text_field(spec.get("domain"))
            sub_domain = _text_field(spec.get("sub_domain"))
            confidence = _confidence_value(spec.get("confidence"))
        if domain:
            parsed[prefix] = (domain, sub_domain, confidence)
    return parsed
def _as_layer_map(value: Any) -> dict[str, int]:
    if not isinstance(value, dict) or not value:
        return {}
    parsed: dict[str, int] = {}
    for key, val in value.items():
        if not isinstance(key, str) or not key:
            return {}
        if not isinstance(val, int) or isinstance(val, bool) or val < 0:
            return {}
        parsed[key] = val
    return parsed
@dataclass(frozen=True)
class SkillProfile:
    name: str
    root: str
    source: str = _DEFAULT_PROFILE_SOURCE
    orchestrator_modules: Mapping[str, str] = field(default_factory=dict)
    domain_prefixes: Mapping[str, tuple[str, str, float]] = field(default_factory=dict)
    infra_modules: tuple[str, ...] = ()
    layer_map: Mapping[str, int] = field(default_factory=dict)
    sca_self_kernel: frozenset[str] = frozenset()
    def to_dict(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "root": self.root,
            "source": self.source,
            "orchestrator_modules": dict(self.orchestrator_modules),
            "domain_prefixes": {
                key: list(value) for key, value in self.domain_prefixes.items()
            },
            "infra_modules": list(self.infra_modules),
            "layer_map": dict(self.layer_map),
            "sca_self_kernel": sorted(self.sca_self_kernel),
        }
def is_appledouble_basename(base: str) -> bool:
    return str(base or "").startswith("._")
def is_scan_py_name(filename: str) -> bool:
    name = str(filename or "")
    return (name.lower().endswith(".py")
            and not name.startswith(".")
            and not is_appledouble_basename(name))
def is_test_source_name(name: str) -> bool:
    lowered = str(name or "").lower()
    return lowered.startswith("test_") or lowered.endswith("_test.py")
def _is_product_py_name(name: str) -> bool:
    return (is_scan_py_name(name)
            and name.lower() != "conftest.py"
            and not is_test_source_name(name))
_TEMP_ARTIFACT_DIR_RE = re.compile(r"^tmp[a-z0-9_]{4,}$")
def is_temp_artifact_dir(name: str) -> bool:
    return bool(_TEMP_ARTIFACT_DIR_RE.match(str(name or "").lower()))
_PATH_TEXT_ERRORS = (TypeError, ValueError, UnicodeDecodeError, OSError)
def _raw_path_text(path: Any) -> str:
    if isinstance(path, (bytes, bytearray)):
        raw: Any = bytes(path)
    elif isinstance(path, os.PathLike):
        raw = path
    elif isinstance(path, str):
        return path
    else:
        return ""
    try:
        return os.fsdecode(raw)
    except _PATH_TEXT_ERRORS as exc:
        log_swallowed(
            __name__, exc, context=f"_raw_path_text:{type(exc).__name__}")
        return ""
def _normalize_root(skill_dir: Any) -> str:
    skill_dir = _raw_path_text(skill_dir)
    if not skill_dir.strip():
        return ""
    try:
        root = os.path.realpath(os.path.abspath(skill_dir))
    except (OSError, ValueError) as exc:
        log_swallowed(
            __name__, exc, context=f"_normalize_root:{type(exc).__name__}")
        return ""
    return root if os.path.isdir(root) else ""
def self_skill_root() -> str:
    return _SELF_ROOT
def is_self_skill(skill_dir: Any) -> bool:
    root = _normalize_root(skill_dir)
    return bool(root) and os.path.normcase(root) == os.path.normcase(_SELF_ROOT)
def _file_state(path: str) -> tuple[Any, ...]:
    digest = hashlib.sha256()
    try:
        with open(path, "rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except FileNotFoundError:
        return ("missing",)
    except OSError as exc:
        log_swallowed(__name__, exc, context=f"_file_state:{type(exc).__name__}")
        return ("missing",)
    return ("present", digest.hexdigest())
def _read_json_declaration(root: str, *, strict: bool) -> dict[str, Any] | None:
    path = os.path.join(root, PROFILE_FILENAME)
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError,
            RecursionError, MemoryError) as exc:
        if strict:
            raise SkillProfileError(
                f"技能画像声明不可解析: {path}: {exc}") from exc
        log_swallowed(
            __name__, exc, context=f"_read_json_declaration:{type(exc).__name__}")
        _log.warning("[skill_profile] 声明损坏，降级为通用派生: %s: %s",
                     path, exc)
        return None
    if not isinstance(payload, dict):
        if strict:
            raise SkillProfileError(f"技能画像声明必须是对象: {path}")
        _log.warning("[skill_profile] 声明不是对象，降级为通用派生: %s", path)
        return None
    schema = payload.get("schema")
    if schema not in (None, PROFILE_SCHEMA):
        if strict:
            raise SkillProfileError(
                f"未知画像格式版本: {schema!r}（期望 {PROFILE_SCHEMA}）")
        _log.warning("[skill_profile] 未知画像格式版本 %r，降级为通用派生: %s",
                     schema, path)
        return None
    return payload
_KNOWN_DEBT_KEY = "known_debt"
_KNOWN_DEBT_KINDS: tuple[str, ...] = ("language_assumption", "self_privilege")
def _declared_known_debt(root: str, kind: str) -> frozenset[str]:
    if kind not in _KNOWN_DEBT_KINDS:
        return frozenset()
    payload = _read_json_declaration(root, strict=False)
    if not isinstance(payload, Mapping):
        return frozenset()
    debt = payload.get(_KNOWN_DEBT_KEY)
    if not isinstance(debt, Mapping):
        return frozenset()
    values = debt.get(kind)
    if not isinstance(values, (list, tuple, set, frozenset)):
        return frozenset()
    return frozenset(
        item.strip() for item in values
        if isinstance(item, str) and item.strip())
def _read_source_text(path: str) -> str:
    with tokenize.open(path) as handle:
        return handle.read()
def _from_declaration(root: str, payload: Mapping[str, Any]) -> SkillProfile:
    name = payload.get("name")
    return SkillProfile(
        name=(name.strip() if isinstance(name, str) and name.strip()
              else os.path.basename(root)),
        root=root,
        source="declared",
        orchestrator_modules=_as_str_map(payload.get("orchestrator_modules")),
        domain_prefixes=_as_prefix_map(payload.get("domain_prefixes")),
        infra_modules=_as_str_tuple(payload.get("infra_modules")),
        layer_map=_as_layer_map(payload.get("layer_map")),
        sca_self_kernel=frozenset(
            _as_str_tuple(payload.get("sca_self_kernel"))),
    )
def _require_root(skill_dir: Any) -> str:
    root = _normalize_root(skill_dir)
    if not root:
        raise SkillProfileError(f"技能目录不可用: {skill_dir!r}")
    return root
def _empty_profile(root: str, *, source: str = _DEFAULT_PROFILE_SOURCE,
                   name: str | None = None) -> SkillProfile:
    return SkillProfile(
        name=os.path.basename(root) if name is None else name,
        root=root,
        source=source,
    )
def _clone_profile(profile: SkillProfile) -> SkillProfile:
    return SkillProfile(
        name=profile.name,
        root=profile.root,
        source=profile.source,
        orchestrator_modules=dict(profile.orchestrator_modules),
        domain_prefixes=dict(profile.domain_prefixes),
        infra_modules=profile.infra_modules,
        layer_map=dict(profile.layer_map),
        sca_self_kernel=profile.sca_self_kernel,
    )
def _fallback_profile(skill_dir: Any) -> SkillProfile:
    raw = _raw_path_text(skill_dir).rstrip("/\\")
    return _empty_profile("", name=os.path.basename(raw))
def load_declared_profile(
        skill_dir: Any, *, strict: bool = _DEFAULT_STRICT) -> SkillProfile | None:
    root = _require_root(skill_dir) if strict else _normalize_root(skill_dir)
    if not root:
        return None
    payload = _read_json_declaration(root, strict=strict)
    return _from_declaration(root, payload) if payload is not None else None
def resolve_skill_profile(
        skill_dir: Any, *, strict: bool = _DEFAULT_STRICT) -> SkillProfile:
    root = _require_root(skill_dir) if strict else _normalize_root(skill_dir)
    if not root:
        return _fallback_profile(skill_dir)
    fingerprint = (_file_state(os.path.join(root, PROFILE_FILENAME)),)
    if not strict:
        with _PROFILE_LOCK:
            cached = _PROFILE_CACHE.get(root)
            if cached is not None and cached[0] == fingerprint:
                return _clone_profile(cached[1])
    declared = load_declared_profile(root, strict=strict)
    if declared is not None:
        profile = declared
    else:
        profile = _empty_profile(
            root, source="self" if is_self_skill(root) else "derived")
    if not strict:
        with _PROFILE_LOCK:
            _PROFILE_CACHE[root] = (fingerprint, _clone_profile(profile))
    return profile
def reset_profile_cache() -> None:
    with _PROFILE_LOCK:
        _PROFILE_CACHE.clear()
def profile_diagnostics(skill_dir: Any) -> dict[str, Any]:
    root = _normalize_root(skill_dir)
    if not root:
        return {"ok": False, "error": f"技能目录不可用: {skill_dir!r}"}
    profile = resolve_skill_profile(root)
    return {
        "ok": True,
        "root": root,
        "source": profile.source,
        "declaration": (
            PROFILE_FILENAME
            if os.path.isfile(os.path.join(root, PROFILE_FILENAME))
            else ""
        ),
        "orchestrator_modules": len(profile.orchestrator_modules),
        "domain_prefixes": len(profile.domain_prefixes),
        "infra_modules": len(profile.infra_modules),
        "layer_map": len(profile.layer_map),
        "sca_self_kernel": len(profile.sca_self_kernel),
    }
LAYOUT_FLAT = "flat"
LAYOUT_SCRIPTS = "scripts"
LAYOUT_SRC = "src"
LAYOUT_DOC = "doc"
LAYOUT_EMPTY = "empty"
LAYOUT_OTHER = "other"
LANGUAGE_BY_SUFFIX: dict[str, str] = {
    ".py": "python", ".pyx": "python", ".pyi": "python", ".pyw": "python",
    ".js": "javascript", ".jsx": "javascript", ".mjs": "javascript",
    ".cjs": "javascript",
    ".ts": "typescript", ".tsx": "typescript", ".mts": "typescript",
    ".cts": "typescript",
    ".md": "markdown", ".mdx": "markdown", ".rst": "markdown",
    ".yml": "yaml", ".yaml": "yaml",
    ".json": "json", ".json5": "json", ".jsonc": "json",
    ".toml": "toml", ".ini": "ini", ".cfg": "ini", ".conf": "ini",
    ".html": "html", ".htm": "html", ".xml": "xml", ".svg": "xml",
    ".css": "css", ".scss": "css", ".sass": "css", ".less": "css",
    ".sh": "shell", ".bash": "shell", ".zsh": "shell", ".fish": "shell",
    ".bat": "batch", ".cmd": "batch", ".ps1": "powershell", ".psm1": "powershell",
    ".txt": "text", ".csv": "data", ".tsv": "data",
    ".sql": "sql", ".psql": "sql",
    ".c": "c", ".h": "c", ".cpp": "cpp", ".hpp": "cpp", ".cc": "cpp",
    ".cxx": "cpp",
    ".rs": "rust", ".go": "go", ".java": "java", ".scala": "scala",
    ".kt": "kotlin", ".kts": "kotlin", ".swift": "swift",
    ".r": "r", ".rmd": "r",
    ".lua": "lua", ".rb": "ruby", ".php": "php",
    ".pl": "perl", ".pm": "perl", ".cs": "csharp",
    ".dart": "dart", ".ex": "elixir", ".exs": "elixir",
    ".hs": "haskell", ".ml": "ocaml", ".mli": "ocaml",
    ".ipynb": "jupyter",
    ".lock": "lockfile",
    ".proto": "protobuf",
}
CODE_LANGUAGES: frozenset[str] = frozenset({
    "python", "javascript", "typescript", "go", "rust", "java", "scala",
    "kotlin", "swift", "ruby", "php", "perl", "lua", "dart", "elixir",
    "haskell", "ocaml", "c", "cpp", "csharp", "r", "shell", "batch",
    "powershell", "sql", "protobuf", "jupyter",
})
_ECOSYSTEM_MARKERS: tuple[tuple[str, str], ...] = (
    ("tsconfig.json", "typescript"),
    ("package.json", "javascript"),
    ("go.mod", "go"),
    ("cargo.toml", "rust"),
    ("pom.xml", "java"),
    ("build.gradle.kts", "kotlin"),
    ("build.gradle", "java"),
    ("gemfile", "ruby"),
    ("composer.json", "php"),
    ("mix.exs", "elixir"),
    ("pubspec.yaml", "dart"),
    ("cmakelists.txt", "cpp"),
)
_CODE_DIR_NAMES = ("src", "lib", "app", "pkg", "cmd", "internal",
                     "source", "scripts")
ENTRYPOINT_STEMS: frozenset[str] = frozenset({
    "__main__", "main", "cli", "__cli__",
})
SOURCE_DIR_NAMES = ("src",)
_DOC_SUFFIXES = (".md", ".markdown", ".rst", ".txt")
@dataclass(frozen=True)
class SkillLayout:
    root: str
    kind: str = LAYOUT_EMPTY
    package_name: str = ""
    package_root: str = ""
    modules: tuple[str, ...] = ()
    scripts: tuple[str, ...] = ()
    entrypoints: tuple[str, ...] = ()
    docs: tuple[str, ...] = ()
    source_files: tuple[str, ...] = ()
    languages: tuple[str, ...] = ()
    has_frontmatter_skill: bool = False
    @property
    def primary_language(self) -> str:
        return self.languages[0] if self.languages else ""
    @property
    def is_package(self) -> bool:
        return bool(self.package_name and self.package_root)
    @property
    def has_code(self) -> bool:
        if self.kind == LAYOUT_OTHER:
            return bool(self.source_files or self.languages)
        return self.is_package or bool(
            self.modules or self.scripts or self.entrypoints)
    @property
    def analysable_scripts(self) -> tuple[str, ...]:
        if self.kind == LAYOUT_SCRIPTS:
            return tuple(dict.fromkeys((*self.scripts, *self.entrypoints)))
        if self.kind in (LAYOUT_FLAT, LAYOUT_SRC):
            return self.entrypoints
        return ()
    def to_dict(self) -> dict[str, Any]:
        return {
            "root": self.root,
            "kind": self.kind,
            "package_name": self.package_name,
            "package_root": self.package_root,
            "modules": list(self.modules),
            "scripts": list(self.scripts),
            "entrypoints": list(self.entrypoints),
            "docs": list(self.docs),
            "source_files": list(self.source_files),
            "languages": list(self.languages),
            "primary_language": self.primary_language,
            "has_frontmatter_skill": self.has_frontmatter_skill,
            "is_package": self.is_package,
            "has_code": self.has_code,
        }
def _list_py(directory: str, *, skip_dunder: bool = True) -> tuple[str, ...]:
    try:
        names = os.listdir(directory)
    except OSError as exc:
        log_swallowed(__name__, exc, context=f"_list_py:{type(exc).__name__}")
        return ()
    found: list[str] = []
    for name in sorted(names):
        if not is_scan_py_name(name):
            continue
        if skip_dunder and name.startswith("__"):
            continue
        if os.path.isfile(os.path.join(directory, name)):
            found.append(name)
    return tuple(found)
def _list_docs(directory: str) -> tuple[str, ...]:
    try:
        names = os.listdir(directory)
    except OSError as exc:
        log_swallowed(
            __name__, exc, context=f"_list_docs:{type(exc).__name__}")
        return ()
    return tuple(
        name for name in sorted(names)
        if not name.startswith(".")
        and name.lower().endswith(_DOC_SUFFIXES)
        and os.path.isfile(os.path.join(directory, name))
    )
def _iter_scripts(scripts_dir: str) -> tuple[str, ...]:
    if not os.path.isdir(scripts_dir):
        return ()
    return tuple(
        f"scripts/{name}"
        for name in _list_py(scripts_dir, skip_dunder=False)
        if _is_product_py_name(name) and name != "__init__.py"
    )
_TOP_LEVEL_PACKAGE_SKIP: frozenset[str] = frozenset({
    "tests", "test", "testing", "docs", "doc", "examples", "example",
    "scripts", "script", "tools", "tool", "build", "dist", "node_modules",
    "venv", "temp", "tmp", "log", "logs",
})
def _declared_project_name(root: str) -> str:
    path = os.path.join(root, "pyproject.toml")
    if not os.path.isfile(path):
        return ""
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            payload = tomllib.loads(handle.read())
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        log_swallowed(
            __name__, exc, context=f"_declared_project_name:{type(exc).__name__}")
        return ""
    tool = payload.get("tool")
    poetry = tool.get("poetry") if isinstance(tool, Mapping) else None
    for section in (payload.get("project"), poetry):
        if not isinstance(section, Mapping):
            continue
        name = section.get("name")
        if isinstance(name, str) and name.strip():
            return name.strip().replace("-", "_").replace(".", "_")
    return ""
def _is_importable_package_name(name: str) -> bool:
    return bool(name) and name.isidentifier() and not keyword.iskeyword(name)
def _project_name_hint(root: str) -> str:
    hinted = (_declared_project_name(root)
              or os.path.basename(root).replace("-", "_"))
    return hinted if _is_importable_package_name(hinted) else ""
def _select_package(base_dir: str, candidates: list[str],
                    hint: str) -> tuple[str, str]:
    if not candidates:
        return "", ""
    if len(candidates) == 1:
        name = candidates[0]
        return name, os.path.join(base_dir, name)
    if hint and hint in candidates:
        return hint, os.path.join(base_dir, hint)
    sized = sorted(
        ((len(_module_stems(os.path.join(base_dir, name))), name)
         for name in candidates),
        key=lambda item: (-item[0], item[1]))
    if sized[0][0] > 0 and sized[0][0] > sized[1][0]:
        name = sized[0][1]
        return name, os.path.join(base_dir, name)
    return "", ""
def _has_product_py_recursive(package_root: str) -> bool:
    def _onerror(exc: OSError) -> None:
        log_swallowed(
            __name__, exc, context=f"_has_product_py_recursive:{type(exc).__name__}")
    for dirpath, dirnames, filenames in os.walk(package_root, onerror=_onerror):
        dirnames[:] = sorted(
            name for name in dirnames
            if _is_importable_package_name(name)
            and not _is_non_product_dir(os.path.join(dirpath, name), name))
        if any(_is_product_py_name(name)
               and os.path.isfile(os.path.join(dirpath, name))
               for name in filenames):
            return True
    return False
def _top_level_package(root: str) -> tuple[str, str]:
    try:
        children = sorted(os.listdir(root))
    except OSError as exc:
        log_swallowed(
            __name__, exc, context=f"_top_level_package:{type(exc).__name__}")
        return "", ""
    regular_candidates: list[str] = []
    namespace_candidates: list[str] = []
    for child in children:
        if (not _is_importable_package_name(child)
                or child.lower() in _TOP_LEVEL_PACKAGE_SKIP
                or _is_non_product_dir(os.path.join(root, child), child)):
            continue
        package_root = os.path.join(root, child)
        if not os.path.isdir(package_root):
            continue
        if os.path.isfile(os.path.join(package_root, "__init__.py")):
            regular_candidates.append(child)
        elif _has_product_py_recursive(package_root):
            namespace_candidates.append(child)
    hint = _project_name_hint(root)
    candidates = regular_candidates + namespace_candidates
    if hint not in namespace_candidates:
        candidates = regular_candidates or namespace_candidates
    return _select_package(root, candidates, hint)
def _detect_package(root: str) -> tuple[str, str]:
    root_name = os.path.basename(root)
    if (os.path.isfile(os.path.join(root, "__init__.py"))
            and _is_importable_package_name(root_name)):
        return root_name, root
    for dir_name in SOURCE_DIR_NAMES:
        src_root = os.path.join(root, dir_name)
        if not os.path.isdir(src_root):
            continue
        try:
            children = sorted(os.listdir(src_root))
        except OSError as exc:
            log_swallowed(
                __name__, exc, context=f"_detect_package:{type(exc).__name__}")
            continue
        candidates: list[str] = []
        for child in children:
            if (not _is_importable_package_name(child)
                    or child.lower() in _TOP_LEVEL_PACKAGE_SKIP
                    or _is_non_product_dir(
                        os.path.join(src_root, child), child)):
                continue
            pkg_root = os.path.join(src_root, child)
            if (os.path.isdir(pkg_root)
                    and (os.path.isfile(os.path.join(pkg_root, "__init__.py"))
                         or _has_product_py_recursive(pkg_root))):
                candidates.append(child)
        picked = _select_package(src_root, candidates, _project_name_hint(root))
        if picked[0]:
            return picked
    return _top_level_package(root)
def _has_skill_md(root: str) -> bool:
    return os.path.isfile(os.path.join(root, "SKILL.md"))
def _merge_languages(*groups: tuple[str, ...]) -> tuple[str, ...]:
    ordered: list[str] = []
    for group in groups:
        for language in group:
            if language and language not in ordered:
                ordered.append(language)
    return tuple(ordered)
def _iter_source_paths(base: str, *, recursive: bool):
    if not recursive:
        try:
            names = sorted(os.listdir(base))
        except OSError as exc:
            log_swallowed(
                __name__, exc, context=f"_iter_source_paths:{type(exc).__name__}")
            return
        for name in names:
            path = os.path.join(base, name)
            if os.path.isfile(path):
                yield path
        return
    def _onerror(exc: OSError) -> None:
        log_swallowed(
            __name__, exc, context=f"_iter_source_paths:{type(exc).__name__}")
    for dirpath, dirnames, filenames in os.walk(base, onerror=_onerror):
        dirnames[:] = sorted(
            name for name in dirnames
            if not _is_non_product_dir(os.path.join(dirpath, name), name))
        for name in sorted(filenames):
            yield os.path.join(dirpath, name)
def _detect_code_sources(root: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    weights: dict[str, int] = {}
    files: list[str] = []
    seen: set[str] = set()
    bases = [(root, False)]
    bases.extend((os.path.join(root, name), True) for name in _CODE_DIR_NAMES)
    for base, recursive in bases:
        if not os.path.isdir(base):
            continue
        for path in _iter_source_paths(base, recursive=recursive):
            name = os.path.basename(path)
            if name.startswith("."):
                continue
            suffix = os.path.splitext(name)[1].lower()
            language = LANGUAGE_BY_SUFFIX.get(suffix, "")
            if language not in CODE_LANGUAGES or suffix == ".py":
                continue
            relative = os.path.relpath(path, root).replace("\\", "/")
            if relative in seen:
                continue
            seen.add(relative)
            files.append(relative)
            try:
                weights[language] = (weights.get(language, 0)
                                     + os.path.getsize(path))
            except OSError as exc:
                log_swallowed(
                    __name__, exc,
                    context=f"_detect_code_sources:{type(exc).__name__}")
                weights[language] = weights.get(language, 0) + 1
    ordered = tuple(sorted(weights, key=lambda lang: (-weights[lang], lang)))
    return tuple(files), ordered
def _detect_ecosystem_language(root: str) -> str:
    try:
        names = {name.lower() for name in os.listdir(root)}
    except OSError as exc:
        log_swallowed(
            __name__, exc, context=f"_detect_ecosystem_language:{type(exc).__name__}")
        return ""
    for marker, language in _ECOSYSTEM_MARKERS:
        if marker in names:
            return language
    return ""
def detect_layout(skill_dir: Any) -> SkillLayout:
    root = _normalize_root(skill_dir)
    if not root:
        return SkillLayout(root="")
    docs = _list_docs(root)
    scripts = _iter_scripts(os.path.join(root, "scripts"))
    package_name, package_root = _detect_package(root)
    root_py = _list_py(root, skip_dunder=False)
    product_root_py = tuple(name for name in root_py if _is_product_py_name(name))
    source_files, source_languages = _detect_code_sources(root)
    if not source_files and not (scripts or package_name or product_root_py):
        ecosystem = _detect_ecosystem_language(root)
        if ecosystem:
            source_languages = (ecosystem,)
    standalone_scripts = (
        tuple(name for name in product_root_py if name != "__init__.py")
        if not package_name or package_root != root else ())
    script_files = tuple(dict.fromkeys((*scripts, *standalone_scripts)))
    python_face: tuple[str, ...] = (
        ("python",) if (script_files or package_name) else ())
    languages = _merge_languages(python_face, source_languages)
    has_other_code = bool(source_files or source_languages)
    package_entrypoints: tuple[str, ...] = ()
    if package_name:
        package_prefix = ""
        if package_root != root:
            package_prefix = os.path.relpath(package_root, root).replace(
                os.sep, "/") + "/"
        package_entrypoints = _entrypoints_of(
            package_root, (), prefix=package_prefix, recursive=True)
    if script_files:
        return SkillLayout(
            root=root,
            kind=LAYOUT_SCRIPTS,
            package_name=package_name,
            package_root=package_root,
            modules=_module_stems(package_root) if package_name else (),
            scripts=script_files,
            entrypoints=tuple(dict.fromkeys((
                *_entrypoints_of(root, script_files), *package_entrypoints))),
            docs=docs,
            source_files=source_files,
            languages=languages,
            has_frontmatter_skill=_has_skill_md(root),
        )
    if package_name and package_root != root:
        return SkillLayout(
            root=root,
            kind=LAYOUT_SRC,
            package_name=package_name,
            package_root=package_root,
            modules=_module_stems(package_root),
            scripts=(),
            entrypoints=package_entrypoints,
            docs=docs,
            source_files=source_files,
            languages=languages,
            has_frontmatter_skill=_has_skill_md(root),
        )
    if package_name:
        return SkillLayout(
            root=root,
            kind=LAYOUT_FLAT,
            package_name=package_name,
            package_root=root,
            modules=_module_stems(root),
            scripts=(),
            entrypoints=package_entrypoints,
            docs=docs,
            source_files=source_files,
            languages=languages,
            has_frontmatter_skill=_has_skill_md(root),
        )
    if has_other_code:
        return SkillLayout(
            root=root,
            kind=LAYOUT_OTHER,
            docs=docs,
            source_files=source_files,
            languages=languages,
            has_frontmatter_skill=_has_skill_md(root),
        )
    if docs:
        return SkillLayout(
            root=root,
            kind=LAYOUT_DOC,
            docs=docs,
            languages=languages,
            has_frontmatter_skill=_has_skill_md(root),
        )
    return SkillLayout(root=root, kind=LAYOUT_EMPTY,
                       languages=languages,
                       has_frontmatter_skill=_has_skill_md(root))
def _layout_belongs_to(layout: Any, root: str) -> bool:
    layout_root = _normalize_root(getattr(layout, "root", ""))
    return bool(layout_root) and os.path.normcase(layout_root) == os.path.normcase(root)
def _path_within_root(path: str, root: str) -> bool:
    try:
        common = os.path.commonpath((path, root))
    except ValueError:
        return False
    return os.path.normcase(common) == os.path.normcase(root)
def python_import_roots(
        skill_dir: Any, layout: SkillLayout | None = None) -> tuple[str, ...]:
    root = _normalize_root(skill_dir)
    if not root:
        return ()
    if layout is None or not _layout_belongs_to(layout, root):
        layout = detect_layout(root)
    package_root = (os.path.realpath(os.path.abspath(layout.package_root))
                    if layout.package_root else "")
    if package_root and not _path_within_root(package_root, root):
        _log.warning("python_import_roots: 忽略技能根外 package_root: %s",
                     package_root)
        package_root = ""
    candidates: list[str] = []
    if package_root:
        candidates.append(os.path.dirname(package_root))
    candidates.append(root)
    src_root = os.path.realpath(os.path.abspath(os.path.join(root, "src")))
    if os.path.isdir(src_root):
        if _path_within_root(src_root, root):
            candidates.append(src_root)
        else:
            _log.warning("python_import_roots: 忽略技能根外 src_root: %s",
                         src_root)
    result: list[str] = []
    seen: set[str] = set()
    for path in candidates:
        key = os.path.normcase(os.path.realpath(path))
        if key in seen:
            continue
        seen.add(key)
        result.append(os.path.realpath(path))
    return tuple(result)
def _module_stems(package_root: str) -> tuple[str, ...]:
    stems: list[str] = []
    for name in _list_py(package_root):
        if _is_product_py_name(name):
            stems.append(name[:-3])
    try:
        children = sorted(os.listdir(package_root))
    except OSError as exc:
        log_swallowed(
            __name__, exc, context=f"_module_stems:{type(exc).__name__}")
        return tuple(stems)
    for child in children:
        if not _is_importable_package_name(child):
            continue
        child_path = os.path.join(package_root, child)
        if _is_non_product_dir(child_path, child):
            continue
        if (os.path.isdir(child_path)
                and (os.path.isfile(os.path.join(child_path, "__init__.py"))
                     or _has_product_py_recursive(child_path))):
            stems.append(child)
    return tuple(dict.fromkeys(stems))
def _entrypoints_of(base_dir: str, scripts: tuple[str, ...], *,
                    prefix: str = "", recursive: bool = False) -> tuple[str, ...]:
    entries: list[str] = []
    if recursive:
        def _onerror(exc: OSError) -> None:
            log_swallowed(__name__, exc, context="_entrypoints_of:OSError")
        for dirpath, dirnames, filenames in os.walk(base_dir, onerror=_onerror):
            dirnames[:] = sorted(
                name for name in dirnames
                if not _is_non_product_dir(os.path.join(dirpath, name), name))
            for name in sorted(filenames):
                stem = name[:-3]
                if (not _is_product_py_name(name)
                        or not (stem in ENTRYPOINT_STEMS
                                or stem.endswith("_cli"))):
                    continue
                relative = os.path.relpath(
                    os.path.join(dirpath, name), base_dir).replace(os.sep, "/")
                entries.append(f"{prefix}{relative}")
    else:
        for name in _list_py(base_dir, skip_dunder=False):
            stem = name[:-3]
            if stem in ENTRYPOINT_STEMS:
                entries.append(f"{prefix}{name}")
    for rel in scripts:
        base = os.path.basename(rel)
        if is_test_source_name(base) or base.lower() == "conftest.py":
            continue
        stem = os.path.splitext(base)[0]
        if stem.endswith("_cli") or stem in ENTRYPOINT_STEMS:
            entries.append(rel)
    return tuple(dict.fromkeys(entries))
_MIN_VOCAB_ENTRIES = 4
_DISPLAY_CONSTANT_WORDS: frozenset[str] = frozenset({
    "MESSAGE", "MESSAGES", "LABEL", "LABELS", "SUGGEST", "SUGGESTION",
    "SUGGESTIONS", "TEMPLATE", "TEMPLATES", "GRADE", "GRADES", "TITLE",
    "TITLES", "HEADER", "HEADERS", "FIX", "FIXES", "GUIDE", "GUIDES",
    "HINT", "HINTS", "REPORT", "REPORTS", "REASON", "REASONS",
})
_DISPLAY_CONSTANT_TAILS: frozenset[str] = frozenset(
    {"TEXT", "NAMES", "STATIC", "RULES"})
def _is_display_constant(name: str) -> bool:
    segments = [seg for seg in str(name or "").strip("_").upper().split("_")
                if seg]
    if not segments:
        return False
    return (any(seg in _DISPLAY_CONSTANT_WORDS for seg in segments)
            or segments[-1] in _DISPLAY_CONSTANT_TAILS)
_CJK_CHAR_RE = re.compile(r"[\u4e00-\u9fff]")
_ASCII_WORD_RE = re.compile(r"[A-Za-z]{3,}")
def _literal_strings(node: Any) -> list[str]:
    collected: list[str] = []
    stack = [node]
    while stack:
        current = stack.pop()
        if isinstance(current, str):
            collected.append(current)
        elif isinstance(current, dict):
            stack.extend(current.keys())
            stack.extend(current.values())
        elif isinstance(current, (list, tuple)):
            stack.extend(current)
        elif isinstance(current, (set, frozenset)):
            stack.extend(sorted(current, key=repr))
    return collected
def _module_string_vocabularies(tree: ast.Module) -> dict[str, list[str]]:
    vocabs: dict[str, list[str]] = {}
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if not isinstance(node.value, (ast.Tuple, ast.List, ast.Set, ast.Dict)):
            continue
        try:
            strings = _literal_strings(ast.literal_eval(node.value))
        except _PARSE_DEGRADE_EXC:
            continue
        targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
        for target in targets:
            if isinstance(target, ast.Name):
                vocabs[target.id] = strings
    return vocabs
def _bilingual_vocabularies(
        vocabs: dict[str, list[str]], tree: ast.Module) -> set[str]:
    ascii_only = {
        name for name, strings in vocabs.items()
        if strings
        and not any(_CJK_CHAR_RE.search(s) for s in strings)
        and any(_ASCII_WORD_RE.search(s) for s in strings)
    }
    if not ascii_only:
        return set()
    bilingual: set[str] = set()
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        used = {child.id for child in walk_nodes(node)
                if isinstance(child, ast.Name) and child.id in vocabs}
        if ascii_only.intersection(used):
            bilingual.update(used)
    return bilingual
_AUDIT_ALWAYS_SKIP_DIRS: frozenset[str] = frozenset({
    "__pycache__", ".git", ".hg", ".svn", ".mypy_cache", ".pytest_cache",
    ".ruff_cache", ".tox", "node_modules", "assets", "references",
})
_AUDIT_RUNTIME_DIR_NAMES: frozenset[str] = frozenset({
    "log", "logs", "temp", "tmp", "jinhua", "build", "dist",
    "env", "env3", "venv", ".venv",
})
_AUDIT_TEST_DIR_NAMES: frozenset[str] = frozenset({"test", "tests"})
def _is_non_product_dir(dirpath: str, name: str) -> bool:
    raw = str(name or "")
    lowered = raw.lower()
    if not lowered or raw.startswith((".", "__")):
        return True
    if lowered in _AUDIT_ALWAYS_SKIP_DIRS or lowered in _AUDIT_TEST_DIR_NAMES:
        return True
    if "backup" in lowered or is_temp_artifact_dir(raw):
        return True
    if lowered in _AUDIT_RUNTIME_DIR_NAMES:
        return not os.path.isfile(os.path.join(dirpath, "__init__.py"))
    return False
def _module_name_of(path: str, root: str) -> str:
    rel = os.path.relpath(path, root).replace(os.sep, "/")
    parts = rel[:-3].split("/")
    if parts and parts[-1] == "__init__":
        parts.pop()
    if not parts:
        parts = [os.path.basename(root)]
    return ".".join(parts)
def _audit_py_sources(root: str) -> list[tuple[str, str]]:
    found: list[tuple[str, str]] = []
    def _onerror(exc: OSError) -> None:
        log_swallowed(
            __name__, exc, context=f"_audit_py_sources:{type(exc).__name__}")
    for dirpath, dirnames, filenames in os.walk(root, onerror=_onerror):
        dirnames[:] = sorted(
            name for name in dirnames
            if not _is_non_product_dir(os.path.join(dirpath, name), name))
        for name in sorted(filenames):
            if (not is_scan_py_name(name)
                    or name.lower() == "conftest.py"
                    or is_test_source_name(name)):
                continue
            path = os.path.join(dirpath, name)
            found.append((_module_name_of(path, root), path))
    return found
def audit_language_assumption(
        skill_dir: Any, *, include_debt: bool = _DEFAULT_INCLUDE_DEBT,
) -> list[dict[str, Any]]:
    root = _normalize_root(skill_dir)
    if not root:
        return []
    findings: list[dict[str, Any]] = []
    debt = _declared_known_debt(root, "language_assumption")
    for module, path in _audit_py_sources(root):
        try:
            tree = ast.parse(_read_source_text(path))
        except (OSError, *_PARSE_DEGRADE_EXC) as exc:
            log_swallowed(
                __name__, exc,
                context=f"audit_language_assumption:{type(exc).__name__}")
            continue
        vocabs = _module_string_vocabularies(tree)
        bilingual = _bilingual_vocabularies(vocabs, tree)
        for constant, strings in vocabs.items():
            if _is_display_constant(constant):
                continue
            if constant in bilingual:
                continue
            cjk = [s for s in strings if _CJK_CHAR_RE.search(s)]
            ascii_words = [s for s in strings
                           if _ASCII_WORD_RE.search(s)
                           and not _CJK_CHAR_RE.search(s)]
            if len(cjk) < _MIN_VOCAB_ENTRIES or ascii_words:
                continue
            qualified = f"{module}.{constant}"
            known_debt = qualified in debt
            if not include_debt and known_debt:
                continue
            findings.append({
                "module": module,
                "constant": constant,
                "qualified": qualified,
                "entries": len(cjk),
                "sample": cjk[:4],
                "in_debt": known_debt,
            })
    return findings
SELF_PRIVILEGE_PATTERNS: tuple[tuple[str, str, str], ...] = (
    ("ZSP-01", "缺省参数回落到自身目录",
     r"\w+\s+or\s+os\.path\.dirname\(\s*os\.path\.(?:abspath|realpath)\(__file__\)\)"),
    ("ZSP-02", "自我豁免名单",
     r"frozenset\(\s*\{\s*os\.path\.realpath\(__file__\)\s*\}\s*\)"),
    ("ZSP-03", "显式自指分支",
     r"if\s+is_(?:self_skill|registry_host)\("),
)
def _executable_text_for_audit(text: str) -> str:
    line_offsets = [0]
    for line in text.splitlines(keepends=True):
        line_offsets.append(line_offsets[-1] + len(line))
    masked = list(text)
    ignored = {
        tokenize.COMMENT,
        tokenize.STRING,
        getattr(tokenize, "FSTRING_MIDDLE", -1),
    }
    try:
        tokens = tokenize.generate_tokens(io.StringIO(text).readline)
        for token in tokens:
            if token.type not in ignored:
                continue
            if token.type == tokenize.STRING:
                prefix = re.match(r"(?i)[rubf]*", token.string).group(0)
                if "f" in prefix.lower():
                    continue
            start = line_offsets[token.start[0] - 1] + token.start[1]
            end = line_offsets[token.end[0] - 1] + token.end[1]
            for pos in range(start, end):
                if masked[pos] not in "\r\n":
                    masked[pos] = " "
    except (tokenize.TokenError, IndentationError, SyntaxError, ValueError) as exc:
        log_swallowed(
            __name__, exc, context=f"_executable_text_for_audit:{type(exc).__name__}")
        failure_line = getattr(exc, "lineno", None)
        if isinstance(exc, tokenize.TokenError) and len(exc.args) > 1:
            location = exc.args[1]
            if (isinstance(location, tuple) and location
                    and isinstance(location[0], int)):
                failure_line = location[0]
        failure_offset = (
            line_offsets[failure_line - 1]
            if isinstance(failure_line, int)
            and 0 <= failure_line - 1 < len(line_offsets) else 0)
        for pos in range(failure_offset, len(masked)):
            if masked[pos] not in "\r\n":
                masked[pos] = " "
    return "".join(masked)
def audit_self_privilege(
        skill_dir: Any, *, include_debt: bool = _DEFAULT_INCLUDE_DEBT,
) -> list[dict[str, Any]]:
    root = _normalize_root(skill_dir)
    if not root:
        return []
    compiled = tuple((rid, label, re.compile(pat, re.MULTILINE))
                     for rid, label, pat in SELF_PRIVILEGE_PATTERNS)
    findings: list[dict[str, Any]] = []
    debt = {
        item.replace("\\", "/")
        for item in _declared_known_debt(root, "self_privilege")
    }
    for _module, path in _audit_py_sources(root):
        rel_path = os.path.relpath(path, root).replace(os.sep, "/")
        if not include_debt and rel_path in debt:
            continue
        try:
            text = _read_source_text(path)
        except (OSError, UnicodeDecodeError, SyntaxError) as exc:
            log_swallowed(
                __name__, exc, context=f"audit_self_privilege:{type(exc).__name__}")
            continue
        executable_text = _executable_text_for_audit(text)
        for rid, label, pattern in compiled:
            for match in pattern.finditer(executable_text):
                line = text.count(chr(10), 0, match.start()) + 1
                findings.append({
                    "rule": rid,
                    "label": label,
                    "file": rel_path,
                    "line": line,
                    "text": match.group(0).strip(),
                })
    return findings

from __future__ import annotations

import ast
import io
import logging
import operator
import os
import tokenize
import types
import typing
import weakref
from collections import Counter
from collections.abc import Callable, Iterator
from dataclasses import (
    MISSING as _MISSING,
)
from dataclasses import (
    asdict,
    dataclass,
    field,
    fields,
    is_dataclass,
)
from typing import NamedTuple

from jwsgj.diag_guard_io import fs_path_text
from jwsgj.diag_module_topology import load_authoritative_layer_map
from jwsgj.diag_shared_ast_nodes import (
    TRY_NODE_TYPES,
    is_dataclass_decorator,
    is_main_check,
    iter_unpack_target_names,
    main_guard_branch,
    str_constant_value,
)
from jwsgj.diag_types_vocab import (
    HARD_MAX_FUNC_LINES,
    LINE_LIMIT,
    MAX_FUNCTION_LINES,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_scope import is_test_file_path, skill_root_of
from jwsgj.skill_profile import (
    SkillProfileError,
    resolve_skill_profile,
)

logger = logging.getLogger(__name__)
class DefectType:
    ALL_OVERWRITE = "all_overwrite"
    ALL_NO_BASE = "all_no_base"
    UNDEFINED_NAME = "undefined_name"
    IMPORT_OVERRIDE = "import_override"
    SYMBOL_CONFLICT = "symbol_conflict"
    MERGE_RESIDUE = "merge_residue"
    DEAD_CODE = "dead_code"
    MISSING_ALL = "missing_all"
    DUPLICATE_IMPORT = "duplicate_import"
    CIRCULAR_IMPORT = "circular_import"
    LAYER_VIOLATION = "layer_violation"
    OVER_LIMIT = "over_limit"
    SYNTAX_ERROR = "syntax_error"
    READ_ERROR = "read_error"
    MISSING_DOCSTRING = "missing_docstring"
    BROAD_EXCEPT = "broad_except"
    SUSPICIOUS_NAMING = "suspicious_naming"
class DomainCategory:
    L0_BASE = "L0_base"
    L1_GUARD = "L1_guard"
    L2_CHECK = "L2_check"
    L3_ENGINE = "L3_engine"
    L4_BUILD = "L4_build"
    L5_ORCHESTRATE = "L5_orchestrate"
    TEST = "test"
    CONFIG = "config"
    SCRIPT = "script"
    UNKNOWN = "unknown"
class VerdictLevel:
    HEALTHY = "healthy"
    MINOR = "minor"
    MODERATE = "moderate"
    SERIOUS = "serious"
    CRITICAL = "critical"
@dataclass
class FunctionInfo:
    name: str = ""
    lineno: int = 0
    end_lineno: int = 0
    args: list[str] = field(default_factory=list)
    decorators: list[str] = field(default_factory=list)
    docstring: str = ""
    complexity: int = 0
    is_async: bool = False
    is_method: bool = False
@dataclass
class ClassInfo:
    name: str = ""
    lineno: int = 0
    end_lineno: int = 0
    bases: list[str] = field(default_factory=list)
    decorators: list[str] = field(default_factory=list)
    methods: list[FunctionInfo] = field(default_factory=list)
    docstring: str = ""
@dataclass
class ImportInfo:
    source: str = ""
    names: list[str] = field(default_factory=list)
    alias: str = ""
    lineno: int = 0
    is_from: bool = False
    source_names: list[str] = field(default_factory=list)
def import_source(imp) -> str:
    src = imp.get("source", "") if isinstance(imp, dict) else getattr(imp, "source", "")
    return src if isinstance(src, str) else ""
def import_is_from(imp) -> bool:
    if isinstance(imp, dict):
        return bool(imp.get("is_from", False))
    return bool(getattr(imp, "is_from", False))
def import_names(imp) -> list:
    names = imp.get("names") if isinstance(imp, dict) else getattr(imp, "names", None)
    if not isinstance(names, list):
        return []
    return [n for n in names if isinstance(n, str)]
def import_source_names(imp) -> list:
    names = (imp.get("source_names") if isinstance(imp, dict)
             else getattr(imp, "source_names", None))
    if not isinstance(names, list) or not names:
        return import_names(imp)
    return [n for n in names if isinstance(n, str)]
def _path_text(value) -> str:
    if not isinstance(value, (str, bytes, os.PathLike)):
        return ""
    return fs_path_text(value)
def module_stem(filepath) -> str:
    filepath = _path_text(filepath)
    if not filepath:
        return ""
    stem = filepath.rsplit("/", 1)[-1].rsplit("\\", 1)[-1]
    if stem.lower().endswith(".py"):
        return stem[:-3]
    return stem
@dataclass
class GlobalVarInfo:
    name: str = ""
    lineno: int = 0
    value_preview: str = ""
def _nn(v, default):
    return default if v is None else v
_ANN_KIND: dict = {
    "bool": "bool",
    "int": "int",
    "float": "float",
    "str": "str",
}
def _top_level_union_members(text: str, separator: str = "|") -> list[str]:
    members: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(depth - 1, 0)
        elif char == separator and depth == 0:
            members.append(text[start:index].strip())
            start = index + 1
    members.append(text[start:].strip())
    return members
_OPTIONAL_TEXT_HEADS = ("Optional[", "typing.Optional[")
_UNION_TEXT_HEADS = ("Union[", "typing.Union[")
def _optional_text_inner(text: str) -> str | None:
    for head in _OPTIONAL_TEXT_HEADS:
        if text.startswith(head) and text.endswith("]"):
            return text[len(head):-1].strip()
    return None
def _single_member_text(ann: str) -> str | None:
    text = ann.strip()
    if (len(text) >= 2 and text[0] == text[-1]
            and text[0] in "'\"" and text[0] not in text[1:-1]):
        text = text[1:-1].strip()
    optional = _optional_text_inner(text)
    if optional is not None:
        text = optional
    members = None
    for head in _UNION_TEXT_HEADS:
        if text.startswith(head) and text.endswith("]"):
            members = _top_level_union_members(
                text[len(head):-1], separator=",")
            break
    if members is None and "|" in text:
        members = _top_level_union_members(text)
    if members is not None:
        non_none = [p for p in members if p and p not in ("None", "NoneType")]
        return non_none[0] if len(non_none) == 1 else None
    return text
def _ann_kind_str(ann: str) -> str | None:
    text = _single_member_text(ann)
    return _ANN_KIND.get(text) if text else None
_CONTAINER_KINDS: dict = {
    list: "list",
    dict: "dict",
    "list": "list",
    "List": "list",
    "typing.List": "list",
    "dict": "dict",
    "Dict": "dict",
    "typing.Dict": "dict",
}
def _container_kind_from_type(ann: type) -> str | None:
    for base, kind in _CONTAINER_KINDS.items():
        if isinstance(base, type) and issubclass(ann, base):
            return kind
    return None
def _container_kind_from_text(text: str) -> str | None:
    kind = _CONTAINER_KINDS.get(text)
    if kind is not None:
        return kind
    head = text.split("[", 1)[0] if "[" in text else ""
    return _CONTAINER_KINDS.get(head) if head else None
def _container_kind(ann) -> str | None:
    if isinstance(ann, type):
        return _container_kind_from_type(ann)
    if isinstance(ann, str):
        text = _single_member_text(ann)
        return _container_kind_from_text(text) if text else None
    members = _non_none_members(ann)
    if len(members) == 1:
        return _container_kind(members[0])
    return _CONTAINER_KINDS.get(getattr(ann, "__origin__", None))
def _union_members(ann) -> tuple:
    origin = getattr(ann, "__origin__", None)
    union_type = getattr(types, "UnionType", None)
    if origin is typing.Union or (union_type is not None
                                  and isinstance(ann, union_type)):
        return tuple(getattr(ann, "__args__", None) or ())
    return ()
def _non_none_members(ann) -> tuple:
    return tuple(arg for arg in _union_members(ann)
                 if arg is not type(None))
def _ann_kind(ann) -> str | None:
    if isinstance(ann, type):
        return _ANN_KIND.get(ann.__name__)
    if isinstance(ann, str):
        return _ann_kind_str(ann)
    members = _non_none_members(ann)
    if len(members) == 1:
        return _ann_kind(members[0])
    return None
def _default_kind(d) -> str | None:
    if isinstance(d, bool):
        return "bool"
    if isinstance(d, int):
        return "int"
    if isinstance(d, float):
        return "float"
    if isinstance(d, str):
        return "str"
    return None
def _scalar_type_ok(v, kind: str | None) -> bool:
    if kind == "bool":
        return isinstance(v, bool)
    if kind == "int":
        return isinstance(v, int) and not isinstance(v, bool)
    if kind == "float":
        return isinstance(v, (int, float)) and not isinstance(v, bool)
    if kind == "str":
        return isinstance(v, str)
    return True
_LIST_ELEMENT_SCALARS = frozenset({"int", "float", "bool"})
_ANY_ELEMENT_NAMES = frozenset({
    "any", "object", "self", "none", "nonetype", "typevar", "type",
})
def _element_kind_by_name(name: str) -> str | None:
    text = _single_member_text(name) or ""
    text = text.removeprefix("typing.")
    if not text:
        return None
    if text == "str":
        return "str"
    if text in _LIST_ELEMENT_SCALARS:
        return text
    if text.lower() in _ANY_ELEMENT_NAMES:
        return "any"
    return "dc"
_LIST_TEXT_HEADS = ("list[", "List[", "typing.List[")
def _list_text_inner(text: str) -> str | None:
    if not text.endswith("]"):
        return None
    for head in _LIST_TEXT_HEADS:
        if text.startswith(head):
            return _single_member_text(text[len(head):-1])
    return None
def _list_text_item_kind(text: str) -> str | None:
    single = _single_member_text(text)
    if single is None:
        return None
    if single != text:
        return _list_item_kind(single)
    inner = _list_text_inner(text)
    if inner is None:
        is_list = (_CONTAINER_KINDS.get(text) == "list"
                   or any(text.startswith(head) and text.endswith("]")
                          for head in _LIST_TEXT_HEADS))
        return "any" if is_list else None
    if not inner:
        return None
    if _list_text_inner(inner) is not None:
        return "any"
    return _element_kind_by_name(inner)
def _runtime_list_item_kind(ann) -> str | None:
    if not (ann is list or getattr(ann, "__origin__", None) is list):
        return None
    args = getattr(ann, "__args__", None)
    if not args:
        return "any"
    elem = args[0]
    members = _non_none_members(elem)
    if len(members) > 1:
        return "any"
    if len(members) == 1:
        elem = members[0]
    if getattr(elem, "__origin__", None) is not None:
        return "any"
    return _element_kind_by_name(getattr(elem, "__name__", ""))
def _list_item_kind(ann) -> str | None:
    if isinstance(ann, str):
        return _list_text_item_kind(ann.strip())
    members = _non_none_members(ann)
    if len(members) == 1:
        return _list_item_kind(members[0])
    return _runtime_list_item_kind(ann)
def _is_dc_instance(obj) -> bool:
    return is_dataclass(obj) and not isinstance(obj, type)
def _list_item_keep(x, item_kind: str | None) -> bool:
    if item_kind == "str":
        return isinstance(x, str)
    if item_kind in {"int", "float", "bool"}:
        return _scalar_type_ok(x, item_kind)
    if item_kind == "dc":
        return isinstance(x, dict) or _is_dc_instance(x)
    if item_kind == "any":
        return x is not None
    return (x is not None
            and (isinstance(x, (str, dict)) or _is_dc_instance(x)))
def _dict_list(v) -> list:
    return v if isinstance(v, list) else []
def _nested_dict(v):
    if _is_dc_instance(v):
        v = asdict(v)
    return v if isinstance(v, dict) and v else None
class _FieldSpecs(NamedTuple):
    defaults: dict
    kinds: dict
    list_kinds: dict
    known: frozenset
    containers: dict
def _null_norm_filtered(dct: dict, dc_cls: type) -> dict:
    specs = _field_norm_specs(dc_cls)
    out: dict = {}
    for k, v in dct.items():
        if k in specs.known:
            _norm_one_field(out, k, v, specs)
    return out
def _field_norm_specs(dc_cls: type) -> _FieldSpecs:
    defaults = {}
    kinds: dict = {}
    list_kinds: dict = {}
    containers: dict = {}
    for f in fields(dc_cls):
        if not f.init:
            continue
        container = _container_kind(f.type)
        if container is not None:
            containers[f.name] = container
        if f.default_factory is not _MISSING:
            defaults[f.name] = f.default_factory()
        elif f.default is not _MISSING:
            defaults[f.name] = f.default
            if f.default is None:
                kinds[f.name] = _ann_kind(f.type)
        else:
            kinds[f.name] = _ann_kind(f.type)
        if container == "list":
            list_kinds[f.name] = _list_item_kind(f.type)
    return _FieldSpecs(defaults, kinds, list_kinds,
                       frozenset(defaults) | frozenset(kinds), containers)
def _is_torn_field_value(v, kind) -> bool:
    return kind is not None and not _scalar_type_ok(v, kind)
def _normalized_container_value(v, default, has_default: bool,
                                container: str, item_kind: str | None):
    expected_type = list if container == "list" else dict
    if isinstance(v, expected_type):
        if container == "list":
            return [item for item in v if _list_item_keep(item, item_kind)]
        return dict(v)
    if has_default:
        return default
    return [] if container == "list" else {}
def _norm_one_field(out: dict, k: str, v, specs: _FieldSpecs) -> None:
    d = specs.defaults.get(k)
    has_default = k in specs.defaults
    declared_container = specs.containers.get(k)
    container = ("list" if declared_container == "list"
                 else _container_kind_from_type(type(d)) or declared_container)
    kind = _default_kind(d) if d is not None else specs.kinds.get(k)
    if container is not None:
        out[k] = _normalized_container_value(
            v, d, has_default, container, specs.list_kinds.get(k))
        return
    if _is_torn_field_value(v, kind):
        if d is not None:
            out[k] = d
        return
    out[k] = _nn(v, d)
def _as_dict(d) -> dict:
    if isinstance(d, dict):
        return d
    logger.debug("[A1] from_dict 顶层输入撕裂，归一空 dict: %r", type(d).__name__)
    return {}
def _nested_item_dict(item, dc_cls: type) -> dict | None:
    if isinstance(item, dc_cls):
        return asdict(item)
    return item if isinstance(item, dict) else None
def _rebuild_nested_list(source: dict, key: str, dc_cls: type) -> list:
    rebuilt: list = []
    for item in _dict_list(source.get(key)):
        data = _nested_item_dict(item, dc_cls)
        if data is not None:
            rebuilt.append(dc_cls(**_null_norm_filtered(data, dc_cls)))
    return rebuilt
def _rebuild_classes(source: dict) -> list:
    rebuilt: list = []
    for item in _dict_list(source.get("classes")):
        data = _nested_item_dict(item, ClassInfo)
        if data is None:
            continue
        known = _null_norm_filtered(data, ClassInfo)
        known["methods"] = _rebuild_nested_list(data, "methods", FunctionInfo)
        rebuilt.append(ClassInfo(**known))
    return rebuilt
@dataclass
class FileBasicInfo:
    filepath: str = ""
    abspath: str = ""
    file_size: int = 0
    total_lines: int = 0
    code_lines: int = 0
    comment_lines: int = 0
    blank_lines: int = 0
    functions: list[FunctionInfo] = field(default_factory=list)
    classes: list[ClassInfo] = field(default_factory=list)
    imports: list[ImportInfo] = field(default_factory=list)
    global_vars: list[GlobalVarInfo] = field(default_factory=list)
    has_all: bool = False
    all_symbols: list[str] = field(default_factory=list)
    encoding: str = "utf-8"
    @property
    def function_count(self) -> int:
        return len(self.functions)
    @property
    def class_count(self) -> int:
        return len(self.classes)
    @property
    def import_count(self) -> int:
        return len(self.imports)
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileBasicInfo:
        d = _as_dict(d)
        known = _null_norm_filtered(d, cls)
        known["functions"] = _rebuild_nested_list(d, "functions", FunctionInfo)
        known["classes"] = _rebuild_classes(d)
        known["imports"] = _rebuild_nested_list(d, "imports", ImportInfo)
        known["global_vars"] = _rebuild_nested_list(d, "global_vars", GlobalVarInfo)
        return cls(**known)
@dataclass
class FileFunctionalDomain:
    filepath: str = ""
    domain: str = DomainCategory.UNKNOWN
    confidence: float = 0.0
    reasoning: str = ""
    sub_domain: str = ""
    key_responsibilities: list[str] = field(default_factory=list)
    related_modules: list[str] = field(default_factory=list)
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileFunctionalDomain:
        d = _as_dict(d)
        return cls(**_null_norm_filtered(d, cls))
@dataclass
class FileKeyEntities:
    filepath: str = ""
    public_api: list[str] = field(default_factory=list)
    exported_symbols: list[str] = field(default_factory=list)
    exception_classes: list[str] = field(default_factory=list)
    config_entries: list[str] = field(default_factory=list)
    entry_points: list[str] = field(default_factory=list)
    registered_rules: list[str] = field(default_factory=list)
    decorator_usage: dict[str, int] = field(default_factory=dict)
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileKeyEntities:
        d = _as_dict(d)
        return cls(**_null_norm_filtered(d, cls))
@dataclass
class FileDefect:
    defect_type: str = ""
    severity: str = "P2"
    filepath: str = ""
    lineno: int = 0
    end_lineno: int = 0
    message: str = ""
    suggestion: str = ""
    confidence: float = 0.7
    detail: dict = field(default_factory=dict)
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileDefect:
        d = _as_dict(d)
        return cls(**_null_norm_filtered(d, cls))
@dataclass
class FileVerdict:
    filepath: str = ""
    level: str = VerdictLevel.HEALTHY
    health_score: float = 1.0
    defect_count: int = 0
    p0_count: int = 0
    p1_count: int = 0
    p2_count: int = 0
    p3_count: int = 0
    top_defects: list[FileDefect] = field(default_factory=list)
    suggestions: list[str] = field(default_factory=list)
    needs_split: bool = False
    needs_refactor: bool = False
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileVerdict:
        d = _as_dict(d)
        known = _null_norm_filtered(d, cls)
        known["top_defects"] = _rebuild_nested_list(
            d, "top_defects", FileDefect)
        return cls(**known)
@dataclass
class FileOverallProfile:
    filepath: str = ""
    basic_info: FileBasicInfo | None = None
    functional_domain: FileFunctionalDomain | None = None
    authoritative_layer: int | None = None
    key_entities: FileKeyEntities | None = None
    defects: list[FileDefect] = field(default_factory=list)
    verdict: FileVerdict | None = None
    scanned_at: str = ""
    scanner_version: str = "1.0"
    elapsed_ms: float = 0.0
    def to_dict(self) -> dict:
        return asdict(self)
    @classmethod
    def from_dict(cls, d: dict) -> FileOverallProfile:
        d = _as_dict(d)
        known = _null_norm_filtered(d, cls)
        basic = _nested_dict(d.get("basic_info"))
        known["basic_info"] = FileBasicInfo.from_dict(basic) if basic else None
        func_dom = _nested_dict(d.get("functional_domain"))
        known["functional_domain"] = (FileFunctionalDomain.from_dict(func_dom)
                                       if func_dom else None)
        entities = _nested_dict(d.get("key_entities"))
        known["key_entities"] = (FileKeyEntities.from_dict(entities)
                                 if entities else None)
        known["defects"] = _rebuild_nested_list(d, "defects", FileDefect)
        verdict = _nested_dict(d.get("verdict"))
        known["verdict"] = FileVerdict.from_dict(verdict) if verdict else None
        return cls(**known)
def behavioral_classes(classes) -> list:
    return [
        c for c in classes
        if c.methods
        and not any(is_dataclass_decorator(d) for d in c.decorators)
        and not any(isinstance(b, str) and "Enum" in b for b in c.bases)
    ]
def a1_to_dict(obj: object) -> dict:
    if isinstance(obj, dict):
        return obj
    if (hasattr(obj, "to_dict") and callable(obj.to_dict)
            and not isinstance(obj, type)):
        return obj.to_dict()
    if _is_dc_instance(obj):
        return asdict(obj)
    if hasattr(obj, "__dict__"):
        return dict(obj.__dict__)
    return {"raw": str(obj)[:500]}
def a1_from_dict(data_class: type, d: dict) -> object:
    if isinstance(data_class, type) and is_dataclass(data_class):
        from_dict = getattr(data_class, "from_dict", None)
        if callable(from_dict):
            return from_dict(d)
        return data_class(**_null_norm_filtered(_as_dict(d), data_class))
    return d
BLOCK_CONTAINER_NODES: tuple[type, ...] = (
    ast.If, ast.While, ast.For, ast.AsyncFor, ast.With, ast.AsyncWith,
    ast.Match, *TRY_NODE_TYPES,
)
PREFIX_TO_DOMAIN: dict[str, tuple[str, str, float]] = {
    "__init__":       (DomainCategory.L5_ORCHESTRATE, "package_init", 0.95),
    "__main__":       (DomainCategory.L5_ORCHESTRATE, "entrypoint", 0.90),
    "test_":          (DomainCategory.TEST, "test", 0.90),
    "conftest":       (DomainCategory.TEST, "test", 0.90),
    "engine_":        (DomainCategory.L3_ENGINE, "engine", 0.85),
    "pipeline_":      (DomainCategory.L5_ORCHESTRATE, "pipeline", 0.90),
    "build_":         (DomainCategory.L4_BUILD, "build", 0.80),
    "log_":           (DomainCategory.L0_BASE, "logging", 0.90),
    "runtime_":       (DomainCategory.L0_BASE, "runtime", 0.90),
    "shared_":        (DomainCategory.L0_BASE, "shared", 0.90),
    "common_":        (DomainCategory.L0_BASE, "shared", 0.90),
    "config_":        (DomainCategory.L0_BASE, "config", 0.90),
    "constants_":     (DomainCategory.L0_BASE, "constants", 0.90),
    "types_":         (DomainCategory.L0_BASE, "types", 0.90),
    "report_":        (DomainCategory.L4_BUILD, "report", 0.85),
    "analysis_":      (DomainCategory.L2_CHECK, "analysis", 0.80),
    "refactor_":      (DomainCategory.L3_ENGINE, "refactor", 0.80),
    "fix_":           (DomainCategory.L3_ENGINE, "fix", 0.80),
}
_L0_IMPORT_MAX_SOURCES = 3
_IMPORT_FAMILY_SCORES: dict[str, tuple[tuple[str, float], ...]] = {
    "base": ((DomainCategory.L0_BASE, 0.3), (DomainCategory.L1_GUARD, 0.2)),
    "guard": ((DomainCategory.L2_CHECK, 0.3),),
    "engine": ((DomainCategory.L3_ENGINE, 0.3),),
    "build": ((DomainCategory.L4_BUILD, 0.25),
              (DomainCategory.L5_ORCHESTRATE, 0.2)),
    "check": ((DomainCategory.L2_CHECK, 0.25),),
}
_BASE_IMPORT_TOKENS = frozenset({
    "log", "logger", "logging", "config", "constants", "types",
    "runtime", "shared", "common",
})
_GUARD_IMPORT_TOKENS = frozenset({"guard", "guards", "gate", "gates"})
_ENGINE_IMPORT_TOKENS = frozenset({
    "engine", "engines", "pipeline", "pipelines", "orchestrator",
    "orchestration",
})
_BUILD_IMPORT_TOKENS = frozenset({
    "build", "builder", "factory", "generator", "generate",
})
_CHECK_IMPORT_TOKENS = frozenset({
    "diag", "diagnostics", "check", "checker", "rule", "rules",
    "detector", "detectors", "scanner", "scan",
})
_IMPORT_FAMILIES: tuple[tuple[str, frozenset[str], tuple[str, ...]], ...] = (
    ("base", _BASE_IMPORT_TOKENS, ()),
    ("guard", _GUARD_IMPORT_TOKENS, ()),
    ("engine", _ENGINE_IMPORT_TOKENS,
     ("engine_", "pipeline_", "orchestrat")),
    ("build", _BUILD_IMPORT_TOKENS, ("build_", "factory_", "generate_")),
    ("check", _CHECK_IMPORT_TOKENS,
     ("diag_", "check_", "rule_", "detector_", "scan_")),
)
def _import_stem_family(stem: str) -> str | None:
    if not isinstance(stem, str) or not stem:
        return None
    lowered = stem.lower()
    tokens = set(lowered.split("_"))
    for family, family_tokens, prefixes in _IMPORT_FAMILIES:
        if tokens & family_tokens or lowered.startswith(prefixes):
            return family
    return None
def _low_dependency_sources(sources: set) -> bool:
    return len(sources) <= _L0_IMPORT_MAX_SOURCES
def _match_prefix(name: str,
                  prefixes: dict[str, tuple[str, str, float]] | None = None
                  ) -> tuple[str, str, float] | None:
    table = (PREFIX_TO_DOMAIN if prefixes is None
             else {**PREFIX_TO_DOMAIN, **prefixes})
    if not table:
        return None
    if name in table:
        return table[name]
    ordered = tuple(sorted(table, key=len, reverse=True))
    for prefix in ordered:
        if name.startswith(prefix):
            return table[prefix]
    return None
def _import_domain_sources(imports: list) -> set[str]:
    sources: set[str] = set()
    for imp in imports:
        source = import_source(imp)
        tail = source.rsplit(".", 1)[-1] if source else ""
        if tail:
            sources.add(tail)
        elif source and import_is_from(imp):
            sources.update(name for name in import_source_names(imp)
                           if name and name != "*")
    return sources
def _infer_from_imports(imports: list) -> tuple[str, str, float] | None:
    import_sources = _import_domain_sources(imports)
    families = {_import_stem_family(src) for src in import_sources}
    families.discard(None)
    if not families:
        return None
    if "base" in families and not _low_dependency_sources(import_sources):
        families.discard("base")
    if not families:
        return None
    domain_score: dict[str, float] = {}
    for family in ("base", "guard", "engine", "build", "check"):
        if family not in families:
            continue
        for domain, score in _IMPORT_FAMILY_SCORES[family]:
            domain_score[domain] = max(score, domain_score.get(domain, 0.0))
    if not domain_score:
        return None
    best = max(domain_score, key=domain_score.get)
    return (best, "import_analysis", domain_score[best])
_API_DOMAIN_RULES: tuple[tuple[str, str, float, tuple[tuple[str, str, int], ...]], ...] = (
    (DomainCategory.L0_BASE, "dataclass_heavy", 0.7,
     (("dataclass", ">=", 3), ("func", "<=", 10), ("class", ">=", 2))),
    (DomainCategory.L2_CHECK, "rule_heavy", 0.6,
     (("public", ">=", 10), ("func", ">=", 15), ("import", ">=", 5))),
    (DomainCategory.L3_ENGINE, "engine_heavy", 0.6,
     (("import", ">=", 10), ("class", ">=", 3), ("public", "<=", 5))),
    (DomainCategory.L4_BUILD, "builder_heavy", 0.5,
     (("func", ">=", 20), ("public", ">=", 5), ("public", "<=", 20))),
    (DomainCategory.L5_ORCHESTRATE, "orchestrator", 0.6,
     (("func", "<=", 5), ("import", ">=", 15))),
)
_API_PRED_OPS: dict[str, Callable[[int, int], bool]] = {"<=": operator.le, ">=": operator.ge}
def _dataclass_decorator_count(usage) -> int:
    if not isinstance(usage, dict):
        return 0
    return sum(v for k, v in usage.items()
               if isinstance(v, int) and not isinstance(v, bool)
               and is_dataclass_decorator(k))
def _api_metrics(profile: FileOverallProfile) -> dict[str, int] | None:
    basic = profile.basic_info
    entities = profile.key_entities
    if not basic or not entities:
        return None
    return {
        "func": basic.function_count,
        "class": basic.class_count,
        "import": basic.import_count,
        "public": len(entities.public_api or ()),
        "dataclass": _dataclass_decorator_count(entities.decorator_usage),
    }
def _infer_from_api(profile: FileOverallProfile) -> tuple[str, str, float] | None:
    metrics = _api_metrics(profile)
    if metrics is None:
        return None
    for domain, label, score, predicates in _API_DOMAIN_RULES:
        if all(_API_PRED_OPS[op](metrics[key], threshold)
               for key, op, threshold in predicates):
            return (domain, label, score)
    return None
def _declared_prefixes(filepath: str) -> dict[str, tuple[str, str, float]]:
    filepath = _path_text(filepath)
    if not filepath:
        return {}
    root = skill_root_of(filepath, include_profile_declaration=True)
    if not root:
        return {}
    try:
        return dict(resolve_skill_profile(root).domain_prefixes)
    except (SkillProfileError, OSError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_declared_prefixes:{type(_swallowed_exc).__name__}')
        return {}
def _profile_source_path(profile: FileOverallProfile) -> str:
    basic = profile.basic_info
    if basic:
        abspath = _path_text(basic.abspath)
        if abspath:
            return abspath
    filepath = _path_text(profile.filepath)
    if filepath:
        return filepath
    return _path_text(basic.filepath) if basic else ""
def _collect_domain_candidates(
        profile: FileOverallProfile, declared: dict | None = None,
) -> tuple[tuple[str, str, float] | None, tuple[str, str, float] | None,
           tuple[str, str, float] | None]:
    filepath = _profile_source_path(profile)
    basename = os.path.splitext(os.path.basename(filepath))[0]
    if declared is None:
        declared = _declared_prefixes(filepath)
    prefix_match = _match_prefix(basename, declared or None)
    import_match = None
    if profile.basic_info and profile.basic_info.imports:
        import_match = _infer_from_imports(profile.basic_info.imports)
    return prefix_match, import_match, _infer_from_api(profile)
def _domain_reasoning(prefix_match, import_match, api_match) -> str:
    parts = []
    if prefix_match:
        parts.append(f"文件名前缀匹配: {prefix_match[0]}")
    if import_match:
        parts.append(f"导入模式分析: {import_match[0]}")
    if api_match:
        parts.append(f"API特征分析: {api_match[0]}")
    return "; ".join(parts) if parts else "无明确特征"
def _domain_cache_signature(
        profile: FileOverallProfile, declared: dict) -> tuple:
    basic = profile.basic_info
    entities = profile.key_entities
    source = _profile_source_path(profile)
    imports = (basic.imports or ()) if basic else ()
    functions = (basic.functions or ()) if basic else ()
    classes = (basic.classes or ()) if basic else ()
    public_api = (entities.public_api or ()) if entities else ()
    entry_points = entities.entry_points if entities else ()
    registered_rules = (entities.registered_rules or ()) if entities else ()
    decorator_usage = entities.decorator_usage if entities else None
    import_sources = frozenset(_import_domain_sources(imports))
    filepath = _path_text(profile.filepath)
    return (
        filepath, bool(basic), bool(entities), source,
        tuple(sorted(declared.items())),
        len(functions), len(classes), len(imports), import_sources,
        len(public_api), bool(entry_points), len(registered_rules),
        _dataclass_decorator_count(decorator_usage),
    )
class DomainInferrer:
    def __init__(self):
        self._cache: dict[str, tuple[tuple, FileFunctionalDomain]] = {}
    @staticmethod
    def _cache_key(profile: FileOverallProfile) -> str:
        source = _profile_source_path(profile)
        if not source or not os.path.isabs(source):
            return ""
        return os.path.normcase(os.path.realpath(source))
    def infer(self, profile: FileOverallProfile) -> FileFunctionalDomain:
        filepath = _path_text(profile.filepath)
        key = self._cache_key(profile)
        declared = (_declared_prefixes(_profile_source_path(profile))
                    if key else None)
        signature = (_domain_cache_signature(profile, declared)
                     if key else None)
        cached = self._cache.get(key) if key else None
        if cached is not None and cached[0] == signature:
            return cached[1]
        prefix_match, import_match, api_match = _collect_domain_candidates(
            profile, declared)
        candidates = [m for m in (prefix_match, import_match, api_match) if m]
        if candidates:
            domain, sub_domain, confidence = max(candidates, key=lambda x: x[2])
        else:
            domain, sub_domain, confidence = DomainCategory.UNKNOWN, "", 0.0
        result = FileFunctionalDomain(
            filepath=filepath,
            domain=domain,
            confidence=confidence,
            reasoning=_domain_reasoning(prefix_match, import_match, api_match),
            sub_domain=sub_domain,
            key_responsibilities=self._extract_responsibilities(profile, domain),
            related_modules=[],
        )
        if key:
            self._cache[key] = (signature, result)
        return result
    def _extract_responsibilities(self, profile: FileOverallProfile,
                                  domain: str) -> list[str]:
        basic = profile.basic_info
        if not basic:
            return ["未知"]
        builder = _RESPONSIBILITY_BUILDERS.get(domain)
        return builder(basic, profile.key_entities) if builder else ["未分类模块"]
def _resp_l0_base(basic, entities) -> list[str]:
    out = ["提供基础类型/常量定义"]
    if basic.class_count > 0:
        out.append(f"定义 {basic.class_count} 个类")
    if basic.import_count <= _L0_IMPORT_MAX_SOURCES:
        out.append("零/低依赖底座")
    return out
def _resp_l1_guard(basic, entities) -> list[str]:
    out = ["安全检查/守卫逻辑"]
    if entities and entities.entry_points:
        out.append("提供守卫入口")
    return out
def _resp_l2_check(basic, entities) -> list[str]:
    out = ["规则检查/检测器"]
    if entities and entities.public_api:
        out.append(f"暴露 {len(entities.public_api)} 个检测API")
    return out
def _resp_l3_engine(basic, entities) -> list[str]:
    out = ["引擎/协调逻辑"]
    if entities and entities.registered_rules:
        out.append(f"注册 {len(entities.registered_rules)} 条规则")
    if basic.function_count > 20:
        out.append("复杂引擎逻辑")
    return out
def _resp_l4_build(basic, entities) -> list[str]:
    out = ["构建/组装逻辑"]
    if basic.function_count > 10:
        out.append(f"包含 {basic.function_count} 个函数")
    return out
def _resp_l5_orchestrate(basic, entities) -> list[str]:
    out = ["顶层编排入口"]
    if entities and entities.entry_points:
        out.append("提供一键入口")
    return out
_RESPONSIBILITY_BUILDERS = {
    DomainCategory.L0_BASE: _resp_l0_base,
    DomainCategory.L1_GUARD: _resp_l1_guard,
    DomainCategory.L2_CHECK: _resp_l2_check,
    DomainCategory.L3_ENGINE: _resp_l3_engine,
    DomainCategory.L4_BUILD: _resp_l4_build,
    DomainCategory.L5_ORCHESTRATE: _resp_l5_orchestrate,
    DomainCategory.TEST: lambda basic, entities: ["测试逻辑"],
    DomainCategory.CONFIG: lambda basic, entities: ["配置/提示词定义"],
}
def _layer_module_identity(filepath, skill_dir: str) -> str:
    path = _path_text(filepath).strip()
    root = _path_text(skill_dir)
    if not path:
        return ""
    if os.path.isabs(path):
        if not root:
            return ""
        try:
            path = os.path.relpath(path, root)
        except (TypeError, ValueError):  # jwsgj:silent-ok
            return ""
    normalized = path.replace("\\", "/")
    if normalized.lower().endswith(".py"):
        normalized = normalized[:-3]
    parts = [part for part in normalized.split("/") if part not in ("", ".")]
    if not parts or any(part == ".." for part in parts):
        return ""
    return ".".join(parts)
def ensure_domains(profiles: list[FileOverallProfile],
                   skill_dir: str | None = None) -> None:
    root = _path_text(skill_dir) if skill_dir is not None else ""
    layer_map = _authoritative_layers(root) if root else None
    inferrer = DomainInferrer()
    for p in profiles:
        if not p.functional_domain:
            p.functional_domain = inferrer.infer(p)
        if layer_map is None:
            continue
        identity = _layer_module_identity(_profile_source_path(p), root)
        stem = identity.rsplit(".", 1)[-1] if identity else ""
        layer = layer_map.get(identity)
        if layer is None and stem:
            layer = layer_map.get(stem)
        p.authoritative_layer = layer
def _authoritative_layers(skill_dir) -> dict[str, int] | None:
    root = _path_text(skill_dir)
    if not root:
        return None
    loaded = load_authoritative_layer_map(root)
    if not isinstance(loaded, dict):
        return None
    exact: dict[str, int] = {}
    identities_by_stem: dict[str, set[str]] = {}
    for key, layer in loaded.items():
        identity = _layer_module_identity(key, root)
        if identity and isinstance(layer, int) and not isinstance(layer, bool):
            exact[identity] = layer
            stem = identity.rsplit(".", 1)[-1]
            identities_by_stem.setdefault(stem, set()).add(identity)
    layers = dict(exact)
    for stem, identities in identities_by_stem.items():
        if len(identities) == 1:
            identity = next(iter(identities))
            layers.setdefault(stem, exact[identity])
    return layers
HOT_COMPLEXITY = 80
_MAX_BOOL_EXPRS = 10
_FLAT_CHAIN_MIN_RATIO = 0.8
_FLAT_CHAIN_MAX_DEPTH = 3
_FINE_CHAIN_MAX_AVG_BRANCH = 5.0
_FINE_CHAIN_TINY_BODY_LINES = 6
_FINE_CHAIN_TINY_RATIO = 0.75
_FINE_CHAIN_GUARD_RATIO = 0.7
_FINE_CHAIN_MAX_DEPTH = 4
_GUARD_BODY_MAX_STMTS = 2
_DECLARATIVE_MAX_COMPLEXITY = 1
_BRANCH_NODE_TYPES: tuple[type, ...] = (
    ast.If, ast.While, ast.For, ast.AsyncFor,
    ast.ExceptHandler, ast.match_case, ast.IfExp)
_STMT_BRANCH_NODE_TYPES: tuple[type, ...] = tuple(
    _t for _t in _BRANCH_NODE_TYPES if _t is not ast.IfExp)
_NESTED_SCOPE_TYPES: tuple[type, ...] = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)
_COMPLEXITY_MEMO: weakref.WeakKeyDictionary = weakref.WeakKeyDictionary()
def clear_complexity_memo() -> None:
    _COMPLEXITY_MEMO.clear()
def _lstrip_string_prefix(text: str) -> str:
    while text and text[0] in "fFrRbBuU":
        text = text[1:]
    return text
def _trailing_open_quote(text: str) -> str | None:
    _q = text[:3]
    _rest = text[3:]
    while True:
        _close = _rest.find(_q)
        if _close == -1:
            return _q
        _rest = _rest[_close + 3:]
        _ns = _rest.lstrip()
        if not _ns:
            return None
        if _ns.startswith(('"""', "'''")):
            _q = _ns[:3]
            _rest = _ns[3:]
            continue
        return None
def _str_node_span(node: ast.AST) -> tuple[int, int] | None:
    _t = type(node)
    if not ((_t is ast.Constant and isinstance(node.value, (str, bytes)))
            or _t is ast.JoinedStr):
        return None
    _s = getattr(node, "lineno", None)
    _e = getattr(node, "end_lineno", None)
    if (isinstance(_s, int) and not isinstance(_s, bool)
            and isinstance(_e, int) and not isinstance(_e, bool)
            and _e > _s):
        return (_s + 1, _e)
    return None
def _multiline_str_lines(tree: ast.AST | None) -> frozenset[int]:
    if tree is None:
        return frozenset()
    return frozenset(
        _ln
        for _n in walk_nodes(tree)
        if (_span := _str_node_span(_n)) is not None
        for _ln in range(_span[0], _span[1] + 1))
_FSTRING_START = getattr(tokenize, "FSTRING_START", -1)
_FSTRING_END = getattr(tokenize, "FSTRING_END", -1)
_STRING_GROUP_TRIVIA = frozenset({tokenize.NL, tokenize.COMMENT})
def _tokenized_multiline_str_lines(source: str) -> frozenset[int]:
    spans: list[tuple[int, int]] = []
    group_start: int | None = None
    group_end: int | None = None
    fstring_depth = 0
    fstring_start = 0
    def _close_group() -> None:
        nonlocal group_start, group_end
        if (group_start is not None and group_end is not None
                and group_end > group_start):
            spans.append((group_start, group_end))
        group_start = group_end = None
    def _extend_group(start: int, end: int) -> None:
        nonlocal group_start, group_end
        if group_start is None:
            group_start = start
        group_end = end if group_end is None else max(group_end, end)
    try:
        tokens = tokenize.generate_tokens(io.StringIO(source).readline)
        for token in tokens:
            ttype = token.type
            if ttype == _FSTRING_START:
                if fstring_depth == 0:
                    fstring_start = token.start[0]
                fstring_depth += 1
                _extend_group(token.start[0], token.end[0])
                continue
            if ttype == _FSTRING_END:
                fstring_depth = max(fstring_depth - 1, 0)
                if fstring_depth == 0:
                    _extend_group(fstring_start or token.start[0],
                                  token.end[0])
                continue
            if fstring_depth:
                continue
            if ttype == tokenize.STRING:
                _extend_group(token.start[0], token.end[0])
                continue
            if ttype in _STRING_GROUP_TRIVIA:
                continue
            _close_group()
    except (tokenize.TokenError, IndentationError, SyntaxError) as exc:
        log_swallowed(
            __name__, exc,
            context=f'_tokenized_multiline_str_lines:{type(exc).__name__}')
    _close_group()
    lines: set[int] = set()
    for start, end in spans:
        lines.update(range(start + 1, end + 1))
    return frozenset(lines)
def _physical_lines(source: str) -> list[str]:
    normalized = source.replace("\r\n", "\n").replace("\r", "\n")
    lines = normalized.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines
def count_lines(source: str, tree: ast.Module | None = None) -> tuple[int, int, int, int]:
    lines = _physical_lines(source)
    total = len(lines)
    code = 0
    comment = 0
    blank = 0
    _str_lines = (_multiline_str_lines(tree) if tree is not None
                  else _tokenized_multiline_str_lines(source))
    in_multiline: str | None = None
    for _idx, line in enumerate(lines):
        _lineno = _idx + 1
        stripped = line.strip()
        if in_multiline:
            comment += 1
            if in_multiline in stripped:
                in_multiline = None
            continue
        if _lineno in _str_lines:
            comment += 1
            continue
        if not stripped:
            blank += 1
            continue
        if stripped.startswith("#"):
            comment += 1
            continue
        _tp = _triple_open_line(stripped)
        if _tp is None:
            code += 1
            continue
        _, in_multiline = _tp
        comment += 1
    return total, code, comment, blank
def _triple_open_line(stripped: str) -> tuple[bool, str | None] | None:
    _triple = _lstrip_string_prefix(stripped)
    if not _triple.startswith(('"""', "'''")):
        return None
    return (True, _trailing_open_quote(_triple))
def _complexity_metrics(
    node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> tuple[int, int, int]:
    hit = _COMPLEXITY_MEMO.get(node)
    if hit is not None:
        return hit
    complexity = 1
    max_ops = 0
    total_ops = 0
    stack = list(node.body)
    _pop = stack.pop
    _append = stack.append
    while stack:
        n = _pop()
        t = type(n)
        if t in _NESTED_SCOPE_TYPES:
            continue
        if t in _BRANCH_NODE_TYPES:
            complexity += 1
        elif t is ast.BoolOp:
            ops = len(n.values) - 1
            complexity += ops
            total_ops += ops
            max_ops = max(max_ops, ops)
        for child in ast.iter_child_nodes(n):
            _append(child)
    result = (complexity, max_ops, total_ops)
    _COMPLEXITY_MEMO[node] = result
    return result
def estimate_complexity(node: ast.FunctionDef | ast.AsyncFunctionDef) -> int:
    return _complexity_metrics(node)[0]
def _is_flat_linear_chain(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    depths: list[int] = []
    stack: list[tuple[ast.AST, int]] = []
    for stmt in node.body:
        if isinstance(stmt, _NESTED_SCOPE_TYPES):
            continue
        if isinstance(stmt, _BRANCH_NODE_TYPES):
            depths.append(0)
        stack.append((stmt, 1 if isinstance(stmt, BLOCK_CONTAINER_NODES) else 0))
    while stack:
        n, d = stack.pop()
        for child in ast.iter_child_nodes(n):
            if isinstance(child, _NESTED_SCOPE_TYPES):
                continue
            if isinstance(child, _BRANCH_NODE_TYPES):
                depths.append(d)
            nd = d + 1 if isinstance(child, BLOCK_CONTAINER_NODES) else d
            stack.append((child, nd))
    if not depths:
        return False
    flat = sum(1 for d in depths if d <= 1)
    return (flat / len(depths) >= _FLAT_CHAIN_MIN_RATIO
            and max(depths) <= _FLAT_CHAIN_MAX_DEPTH)
def _branch_base_lineno(branch: ast.AST, end: int) -> int:
    _base = getattr(branch, "lineno", None)
    if _base is None:
        _body = getattr(branch, "body", None)
        _base = (_body[0].lineno if _body
                 and getattr(_body[0], "lineno", None) is not None
                 else (end or 1))
    return _base
def _branch_effective_size(branch: ast.AST, nested: set[int]) -> int:
    end = 0
    stack = [branch]
    while stack:
        cur = stack.pop()
        if cur is not branch and id(cur) in nested:
            continue
        e = getattr(cur, "end_lineno", 0) or 0
        end = max(end, e)
        stack.extend(ast.iter_child_nodes(cur))
    _base = _branch_base_lineno(branch, end)
    return max((end or _base) - _base + 1, 1)
def _is_guard_branch(body: list) -> bool:
    if len(body) > _GUARD_BODY_MAX_STMTS:
        return False
    last = body[-1]
    return isinstance(last, (ast.Return, ast.Raise, ast.Continue,
                             ast.Expr, ast.Assign))
def _nested_scope_ids(node: ast.AST) -> set[int]:
    nested: set[int] = set()
    for sub in walk_nodes(node):
        if isinstance(sub, _NESTED_SCOPE_TYPES) and sub is not node:
            nested.add(id(sub))
    return nested
def _fine_chain_verdict(branch_count: int, branch_sizes: list[int],
                        guard_count: int, tiny_count: int,
                        max_depth: int) -> bool:
    if branch_count == 0:
        return False
    avg_branch = sum(branch_sizes) / branch_count
    guard_ratio = guard_count / branch_count
    tiny_ratio = tiny_count / branch_count
    return (avg_branch <= _FINE_CHAIN_MAX_AVG_BRANCH
            or tiny_ratio >= _FINE_CHAIN_TINY_RATIO
            or (guard_ratio >= _FINE_CHAIN_GUARD_RATIO
                and max_depth <= _FINE_CHAIN_MAX_DEPTH))
def _is_fine_grained_rule_chain(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    nested = _nested_scope_ids(node)
    branch_count = 0
    guard_count = 0
    tiny_count = 0
    max_depth = 0
    branch_sizes: list[int] = []
    stack: list[tuple[ast.AST, int]] = [(node, 0)]
    while stack:
        n, depth = stack.pop()
        for child in ast.iter_child_nodes(n):
            if id(child) in nested:
                continue
            if isinstance(child, _STMT_BRANCH_NODE_TYPES):
                branch_count += 1
                nd = depth + 1
                max_depth = max(max_depth, nd)
                size = _branch_effective_size(child, nested)
                branch_sizes.append(size)
                body = getattr(child, "body", [])
                _dt, _dg = _branch_kind_deltas(body, size)
                tiny_count += _dt
                guard_count += _dg
                stack.append((child, nd))
            else:
                stack.append((child, depth))
    return _fine_chain_verdict(branch_count, branch_sizes, guard_count,
                               tiny_count, max_depth)
def _branch_kind_deltas(body: list, size: int) -> tuple[int, int]:
    if not body:
        return (0, 0)
    tiny = 1 if size <= _FINE_CHAIN_TINY_BODY_LINES else 0
    guard = 1 if _is_guard_branch(body) else 0
    return (tiny, guard)
def _docstring_expr(node: ast.FunctionDef | ast.ClassDef | ast.Module) -> ast.Expr | None:
    if (node.body and isinstance(node.body[0], ast.Expr)
            and isinstance(node.body[0].value, ast.Constant)
            and isinstance(node.body[0].value.value, str)):
        return node.body[0]
    return None
def _docstring_end_line(node: ast.FunctionDef | ast.ClassDef | ast.Module) -> int:
    _d = _docstring_expr(node)
    return (_d.end_lineno or 0) if _d is not None else 0
def _is_string_only_line(s: str) -> bool:
    t = _lstrip_string_prefix(s)
    return (t.startswith(('"""', "'''"))
            or (t.startswith('"') and t.rstrip(",").endswith('"'))
            or (t.startswith("'") and t.rstrip(",").endswith("'")))
def _count_logic_lines(node: ast.FunctionDef | ast.AsyncFunctionDef,
                       lines: list[str]) -> int:
    start = node.lineno
    end = node.end_lineno or node.lineno
    doc_end = _docstring_end_line(node)
    string_lines = _multiline_str_lines(node)
    logic = 0
    for ln in range(start, end + 1):
        if ln <= doc_end or ln in string_lines:
            continue
        s = lines[ln - 1].strip() if ln - 1 < len(lines) else ""
        if not s or s.startswith("#"):
            continue
        if _is_string_only_line(s):
            continue
        logic += 1
    return logic
def extract_docstring(node: ast.FunctionDef | ast.ClassDef | ast.Module) -> str:
    _d = _docstring_expr(node)
    return _d.value.value if _d is not None else ""
def _check_file_lines(lines: list[str], rel_path: str) -> FileDefect | None:
    total = len(lines)
    if total <= LINE_LIMIT:
        return None
    return FileDefect(
        defect_type=DefectType.OVER_LIMIT,
        severity="P1",
        filepath=rel_path,
        lineno=1,
        end_lineno=total,
        message=(f"文件行数 {total} 超过限制 {LINE_LIMIT}：治理候选"
                 "（GOV-01 禁止直接拆分）"),
        suggestion=("按简化逻辑/消除重复/收敛依赖/迁移代码/提取同模块内"
                    f"私有实现治理，把规模收敛到 {LINE_LIMIT} 行以内"),
        confidence=0.95,
        detail={"total_lines": total, "limit": LINE_LIMIT},
    )
def _limit_defect(node: ast.FunctionDef | ast.AsyncFunctionDef, rel_path: str,
                  message: str, suggestion: str, detail: dict) -> FileDefect:
    return FileDefect(
        defect_type=DefectType.OVER_LIMIT,
        severity="P2",
        filepath=rel_path,
        lineno=node.lineno,
        end_lineno=node.end_lineno or node.lineno,
        message=message,
        suggestion=suggestion,
        confidence=0.8,
        detail=detail,
    )
def _check_func_lines(node: ast.FunctionDef | ast.AsyncFunctionDef,
                      lines: list[str], rel_path: str) -> FileDefect | None:
    func_lines = (node.end_lineno or node.lineno) - node.lineno + 1
    if func_lines <= MAX_FUNCTION_LINES:
        return None
    _exempt = (func_lines <= HARD_MAX_FUNC_LINES
               and (estimate_complexity(node) <= _DECLARATIVE_MAX_COMPLEXITY
                    or _count_logic_lines(node, lines) <= MAX_FUNCTION_LINES))
    if _exempt:
        return None
    return _limit_defect(
        node, rel_path,
        f"函数 '{node.name}' 行数 {func_lines} 超过限制 {MAX_FUNCTION_LINES}",
        (f"按简化逻辑/消除重复/提取同模块内私有实现治理 "
         f"'{node.name}'，把函数行数收敛到 {MAX_FUNCTION_LINES} 以内"),
        {"function": node.name, "func_lines": func_lines, "limit": MAX_FUNCTION_LINES})
def _check_func_complexity(node: ast.FunctionDef | ast.AsyncFunctionDef,
                           rel_path: str) -> FileDefect | None:
    complexity, max_bool_chain, bool_total = _complexity_metrics(node)
    branch_cc = complexity - bool_total
    if branch_cc > HOT_COMPLEXITY:
        flat_exempt = (_is_flat_linear_chain(node)
                       or _is_fine_grained_rule_chain(node))
        if not flat_exempt:
            return _limit_defect(
                node, rel_path,
                f"函数 '{node.name}' 圈复杂度 {branch_cc} 超过热点限制 {HOT_COMPLEXITY}",
                (f"简化 '{node.name}' 的分支逻辑（提取卫语句/"
                 f"同模块内私有实现），将圈复杂度降至 {HOT_COMPLEXITY} 以内"),
                {"function": node.name, "complexity": branch_cc,
                 "limit": HOT_COMPLEXITY, "kind": "complexity",
                 "flat_chain_exempt": False})
    if max_bool_chain > _MAX_BOOL_EXPRS:
        return _limit_defect(
            node, rel_path,
            (f"函数 '{node.name}' 含 {max_bool_chain} 个布尔运算符 "
             f"超过限制 {_MAX_BOOL_EXPRS}，单条条件过长"),
            (f"简化 '{node.name}' 的复合条件（提取具名谓词/"
             f"同模块内私有实现），将布尔运算符数量降至 {_MAX_BOOL_EXPRS} 以内"),
            {"function": node.name, "bool_ops": max_bool_chain,
             "limit": _MAX_BOOL_EXPRS, "kind": "bool_exprs"})
    return None
def check_line_limit(tree: ast.Module, rel_path: str,
                      source: str,
                      nodes: list[ast.AST] | None = None) -> list[FileDefect]:
    defects: list[FileDefect] = []
    lines = _physical_lines(source)
    _file_fd = _check_file_lines(lines, rel_path)
    if _file_fd is not None:
        defects.append(_file_fd)
    is_test = is_test_file_path(rel_path)
    _line_defects: list[FileDefect] = []
    _cx_defects: list[FileDefect] = []
    for node in (nodes if nodes is not None else walk_nodes(tree)):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        _fd = _check_func_lines(node, lines, rel_path)
        if _fd is not None:
            _line_defects.append(_fd)
        if is_test:
            continue
        _cx = _check_func_complexity(node, rel_path)
        if _cx is not None:
            _cx_defects.append(_cx)
    defects.extend(_line_defects)
    defects.extend(_cx_defects)
    return defects
__all__ = [
    'ALL_MUTATOR_METHODS',
    'BLOCK_CONTAINER_NODES',
    'HOT_COMPLEXITY',
    'PREFIX_TO_DOMAIN',
    'SCOPE_BOUNDARY_NODES',
    'ClassInfo',
    'DefectType',
    'DomainCategory',
    'DomainInferrer',
    'FileBasicInfo',
    'FileDefect',
    'FileFunctionalDomain',
    'FileKeyEntities',
    'FileOverallProfile',
    'FileVerdict',
    'FunctionInfo',
    'GlobalVarInfo',
    'ImportInfo',
    'VerdictLevel',
    'a1_from_dict',
    'a1_to_dict',
    'behavioral_classes',
    'binds_all_name',
    'check_duplicate_imports',
    'check_import_override',
    'check_line_limit',
    'clear_complexity_memo',
    'count_lines',
    'ensure_domains',
    'estimate_complexity',
    'extract_docstring',
    'extract_key_entities',
    'import_is_from',
    'import_names',
    'import_source',
    'import_source_names',
    'is_all_delete',
    'is_all_name_target',
    'is_all_self_ref_rebind',
    'is_all_walrus_stmt',
    'iter_scope_stmts',
    'module_stem',
    'parse_all',
    'parse_structure',
]
logger.info("engine_a1_structure A1 画像契约、结构解析与功能域分类已加载: %d 项导出", len(__all__))
SCOPE_BOUNDARY_NODES: tuple[type, ...] = (
    ast.Module, ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
)
_VALUE_PREVIEW_MAX = 80
_OVERRIDE_REPORTS: dict[bool, tuple[str, float, str, str]] = {
    True: (
        "P2",
        0.9,
        ("import '{name}' 冗余重绑定本地别名"
         "（同一对象，第 {line} 行已绑定，无行为影响）"),
        "删除冗余 import 或本地别名其一，保留一处绑定即可",
    ),
    False: (
        "P1",
        0.85,
        "import '{name}' 覆盖了本地定义（在第 {line} 行）",
        "为 import 添加别名: from ... import {name} as _{name}",
    ),
}
class _Binding(NamedTuple):
    lineno: int
    dotted: str | None
    is_import: bool
    is_placeholder: bool
class _OverrideScan:
    __slots__ = ("alias_map", "bindings", "defects", "rel_path")
    def __init__(self, rel_path: str) -> None:
        self.rel_path = rel_path
        self.bindings: dict[str, _Binding] = {}
        self.alias_map: dict[str, str] = {}
        self.defects: list[FileDefect] = []
    def bind_local_def(self, name: str, lineno: int, dotted: str | None,
                       placeholder: bool = False) -> None:
        self.bindings[name] = _Binding(lineno, dotted, False, placeholder)
        self.alias_map[name] = dotted or ""
    def bind_assign(self, node: ast.Assign) -> None:
        placeholder = _is_none_placeholder(node.value)
        for target in node.targets:
            dotted = (_resolve_dotted_source(node.value, self.alias_map)
                      if isinstance(target, ast.Name) else None)
            for name in iter_unpack_target_names(target):
                self.bind_local_def(name, node.lineno, dotted, placeholder)
    def bind_ann_assign(self, node: ast.AnnAssign) -> None:
        if isinstance(node.target, ast.Name) and node.value is not None:
            self.bind_local_def(
                node.target.id, node.lineno,
                _resolve_dotted_source(node.value, self.alias_map),
                _is_none_placeholder(node.value))
    def bind_import(self, node: ast.Import) -> None:
        for alias in node.names:
            self._bind_import_alias(node, alias)
    def bind_import_from(self, node: ast.ImportFrom) -> None:
        for alias in node.names:
            self._bind_importfrom_alias(node, alias)
    def _bind_import_alias(self, node: ast.Import, alias: ast.alias) -> None:
        name = alias.asname or alias.name.split(".", 1)[0]
        source = alias.name if alias.asname else name
        self._commit_import(name, source, node.lineno)
    def _bind_importfrom_alias(self, node: ast.ImportFrom,
                               alias: ast.alias) -> None:
        name = alias.asname or alias.name
        prefix = "." * (node.level or 0)
        if node.module:
            dotted = f"{prefix}{node.module}.{alias.name}"
        else:
            dotted = f"{prefix}{alias.name}"
        self._commit_import(name, dotted, node.lineno)
    def _commit_import(self, name: str, source: str, lineno: int) -> None:
        self._report(name, source, lineno)
        self.bindings[name] = _Binding(lineno, source, True, False)
        self.alias_map[name] = source
    def _report(self, name: str, source: str, lineno: int) -> None:
        bound = self.bindings.get(name)
        if bound is None or bound.is_import or bound.is_placeholder:
            return
        bind_line, bound_src = bound.lineno, bound.dotted
        same_object = bound_src == source
        severity, confidence, message, suggestion = (
            _OVERRIDE_REPORTS[same_object])
        self.defects.append(FileDefect(
            defect_type=DefectType.IMPORT_OVERRIDE,
            severity=severity,
            filepath=self.rel_path,
            lineno=lineno,
            message=message.format(name=name, line=bind_line),
            suggestion=suggestion.format(name=name),
            confidence=confidence,
            detail={"overridden_name": name, "local_def_line": bind_line,
                    "same_object": same_object},
        ))
_OVERRIDE_SCAN_HANDLERS: dict[type, Callable[[_OverrideScan, ast.stmt], None]] = {
    ast.Assign: _OverrideScan.bind_assign,
    ast.AnnAssign: _OverrideScan.bind_ann_assign,
    ast.Import: _OverrideScan.bind_import,
    ast.ImportFrom: _OverrideScan.bind_import_from,
}
def check_import_override(tree: ast.Module, rel_path: str) -> list[FileDefect]:
    scan = _OverrideScan(rel_path)
    for node in iter_scope_stmts(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            scan.bind_local_def(node.name, node.lineno, None)
            continue
        _advance = _OVERRIDE_SCAN_HANDLERS.get(type(node))
        if _advance is not None:
            _advance(scan, node)
    return scan.defects
def _resolve_attribute_chain(value: ast.Attribute,
                             alias_map: dict[str, str]) -> str | None:
    parts: list[str] = []
    node: ast.expr = value
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        base = alias_map.get(node.id, node.id)
        if not base:
            return None
        return ".".join([base] + list(reversed(parts)))
    return None
def _resolve_import_module_call(value: ast.Call,
                                 alias_map: dict[str, str]) -> str | None:
    func = value.func
    if isinstance(func, ast.Name):
        callee = alias_map.get(func.id, func.id)
        if callee not in ("import_module", "importlib.import_module"):
            return None
    elif isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name):
        base = alias_map.get(func.value.id, func.value.id)
        if func.attr != "import_module" or base != "importlib":
            return None
    else:
        return None
    first = value.args[0] if value.args else None
    if isinstance(first, ast.Constant) and isinstance(first.value, str):
        return first.value
    return None
def _is_none_placeholder(value: ast.expr) -> bool:
    return isinstance(value, ast.Constant) and value.value is None
def _resolve_dotted_source(value: ast.expr, alias_map: dict[str, str]) -> str | None:
    if isinstance(value, ast.Attribute):
        return _resolve_attribute_chain(value, alias_map)
    if isinstance(value, ast.Name):
        return alias_map.get(value.id) or None
    if isinstance(value, ast.Call):
        return _resolve_import_module_call(value, alias_map)
    return None
def _dup_import_defect(rel_path: str, lineno: int, message: str,
                       detail: dict) -> FileDefect:
    return FileDefect(
        defect_type=DefectType.DUPLICATE_IMPORT,
        severity="P2",
        filepath=rel_path,
        lineno=lineno,
        message=message,
        suggestion="删除重复的 import 语句",
        confidence=0.9,
        detail=detail,
    )
def _dup_import_defs(node: ast.Import, seen: set[tuple[int | str, ...]],
                     scope_desc: dict, rel_path: str) -> list[FileDefect]:
    defects: list[FileDefect] = []
    for alias in node.names:
        name = alias.asname or alias.name.split(".", 1)[0]
        key = (0, alias.name, name)
        if key in seen:
            defects.append(_dup_import_defect(
                rel_path, node.lineno, f"重复导入 '{name}'",
                {"name": name, **scope_desc}))
        seen.add(key)
    return defects
def _dup_importfrom_defs(node: ast.ImportFrom, seen: set[tuple[int | str, ...]],
                         scope_desc: dict, rel_path: str) -> list[FileDefect]:
    defects: list[FileDefect] = []
    module = node.module or ""
    level = node.level or 0
    for alias in node.names:
        name = alias.asname or alias.name
        display_name = (f"{alias.name} as {name}"
                        if name != alias.name else name)
        key = (level, module, alias.name, name)
        if key in seen:
            _msg = (f"重复导入（from {'.' * level}{module} "
                    f"import {display_name}）" if level
                    else f"重复导入 '{module}.{display_name}'")
            defects.append(_dup_import_defect(
                rel_path, node.lineno, _msg,
                {"module": module, "name": name,
                 "source_name": alias.name, **scope_desc}))
        seen.add(key)
    return defects
def _scope_desc(scope: ast.AST) -> dict:
    if isinstance(scope, (ast.FunctionDef, ast.AsyncFunctionDef)):
        return {"scope": "function", "name": scope.name}
    if isinstance(scope, ast.ClassDef):
        return {"scope": "class", "name": scope.name}
    return {"scope": "module"}
def _check_scope_import_dups(scope: ast.AST, scope_desc: dict,
                             rel_path: str) -> list[FileDefect]:
    defects: list[FileDefect] = []
    seen: set[tuple[int | str, ...]] = set()
    for node in iter_scope_stmts(scope):
        if isinstance(node, ast.Import):
            defects.extend(_dup_import_defs(node, seen, scope_desc, rel_path))
        elif isinstance(node, ast.ImportFrom):
            defects.extend(_dup_importfrom_defs(node, seen, scope_desc, rel_path))
    return defects
def check_duplicate_imports(tree: ast.Module, rel_path: str,
                             nodes: list[ast.AST] | None = None) -> list[FileDefect]:
    defects: list[FileDefect] = []
    for scope in (nodes if nodes is not None else walk_nodes(tree)):
        if not isinstance(scope, SCOPE_BOUNDARY_NODES):
            continue
        defects.extend(_check_scope_import_dups(scope, _scope_desc(scope),
                                                rel_path))
    return defects
def _safe_unparse(node: ast.AST) -> str:
    try:
        return ast.unparse(node)
    except RecursionError as _e:
        log_swallowed(__name__, _e, context='_safe_unparse:RecursionError')
        return ""
def _import_infos_from_import(node: ast.Import) -> list[ImportInfo]:
    infos: list[ImportInfo] = []
    for alias in node.names:
        infos.append(ImportInfo(
            source=alias.name,
            names=[alias.asname or alias.name.split(".", 1)[0]],
            alias=alias.asname or "",
            lineno=node.lineno,
            is_from=False,
            source_names=[alias.name],
        ))
    return infos
def _import_info_from_import_from(node: ast.ImportFrom) -> ImportInfo:
    module = "." * (node.level or 0) + (node.module or "")
    names = [alias.asname or alias.name for alias in node.names]
    return ImportInfo(
        source=module,
        names=names,
        lineno=node.lineno,
        is_from=True,
        source_names=[alias.name for alias in node.names],
    )
def _global_var_info(name: str, lineno: int, value: str) -> GlobalVarInfo:
    return GlobalVarInfo(name=name, lineno=lineno,
                         value_preview=value[:_VALUE_PREVIEW_MAX])
def _note_global_vars_from_assign(node: ast.Assign,
                                  global_vars: list[GlobalVarInfo]) -> None:
    preview = _safe_unparse(node.value)
    for target in node.targets:
        for name in iter_unpack_target_names(target):
            global_vars.append(_global_var_info(name, node.lineno, preview))
def _note_global_var_from_annassign(node: ast.AnnAssign,
                                    global_vars: list[GlobalVarInfo]) -> None:
    if isinstance(node.target, ast.Name) and node.value is not None:
        global_vars.append(_global_var_info(
            node.target.id, node.lineno, _safe_unparse(node.value)))
def parse_structure(
    tree: ast.Module
) -> tuple[list[FunctionInfo], list[ClassInfo], list[ImportInfo], list[GlobalVarInfo]]:
    functions: list[FunctionInfo] = []
    classes: list[ClassInfo] = []
    imports: list[ImportInfo] = []
    global_vars: list[GlobalVarInfo] = []
    for node in iter_scope_stmts(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            functions.append(_parse_function(node))
            continue
        if isinstance(node, ast.ClassDef):
            classes.append(_parse_class(node))
            continue
        if isinstance(node, ast.Import):
            imports.extend(_import_infos_from_import(node))
            continue
        if isinstance(node, ast.ImportFrom):
            imports.append(_import_info_from_import_from(node))
            continue
        if isinstance(node, ast.Assign):
            _note_global_vars_from_assign(node, global_vars)
            continue
        if isinstance(node, ast.AnnAssign):
            _note_global_var_from_annassign(node, global_vars)
    return functions, classes, imports, global_vars
def _parse_function(node: ast.FunctionDef | ast.AsyncFunctionDef,
                    is_method: bool = False) -> FunctionInfo:
    args = ([arg.arg for arg in node.args.posonlyargs]
            + [arg.arg for arg in node.args.args])
    if node.args.vararg is not None:
        args.append(node.args.vararg.arg)
    args.extend(arg.arg for arg in node.args.kwonlyargs)
    if node.args.kwarg is not None:
        args.append(node.args.kwarg.arg)
    decorators = [_safe_unparse(d) for d in node.decorator_list]
    docstring = extract_docstring(node)
    complexity = estimate_complexity(node)
    return FunctionInfo(
        name=node.name,
        lineno=node.lineno,
        end_lineno=node.end_lineno or node.lineno,
        args=args,
        decorators=decorators,
        docstring=docstring,
        complexity=complexity,
        is_async=isinstance(node, ast.AsyncFunctionDef),
        is_method=is_method,
    )
def _parse_class(node: ast.ClassDef) -> ClassInfo:
    bases = [_safe_unparse(b) for b in node.bases]
    decorators = [_safe_unparse(d) for d in node.decorator_list]
    docstring = extract_docstring(node)
    methods: list[FunctionInfo] = []
    for child in iter_scope_stmts(node):
        if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
            methods.append(_parse_function(child, is_method=True))
    return ClassInfo(
        name=node.name,
        lineno=node.lineno,
        end_lineno=node.end_lineno or node.lineno,
        bases=bases,
        decorators=decorators,
        methods=methods,
        docstring=docstring,
    )
def _scope_field_lists(container: ast.AST) -> list[tuple[bool, list[ast.AST]]]:
    out: list[tuple[bool, list[ast.AST]]] = []
    for _field, _val in ast.iter_fields(container):
        if not isinstance(_val, list) or not _val:
            continue
        _first = _val[0]
        if isinstance(_first, ast.stmt):
            out.append((True, _val))
        elif isinstance(_first, (ast.ExceptHandler, ast.match_case)):
            out.append((False, _val))
    return out
def iter_scope_stmts(container: ast.AST) -> Iterator[ast.stmt]:
    stack: list[list] = [[_scope_field_lists(container), 0, 0]]
    while stack:
        _frame = stack[-1]
        _lists, _li, _ii = _frame
        if _li >= len(_lists):
            stack.pop()
            continue
        _is_stmts, _lst = _lists[_li]
        if _ii >= len(_lst):
            _frame[1] = _li + 1
            _frame[2] = 0
            continue
        _item = _lst[_ii]
        _frame[2] = _ii + 1
        if _is_stmts:
            yield _item
            if isinstance(_item, BLOCK_CONTAINER_NODES):
                stack.append([_scope_field_lists(_item), 0, 0])
        else:
            stack.append([_scope_field_lists(_item), 0, 0])
def is_all_name_target(node: ast.AST) -> bool:
    return isinstance(node, ast.Name) and node.id == "__all__"
def is_all_walrus_stmt(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.NamedExpr)
            and is_all_name_target(node.value.target))
def _target_binds_all(target: ast.AST) -> bool:
    if is_all_name_target(target):
        return True
    if isinstance(target, ast.Starred):
        return _target_binds_all(target.value)
    if isinstance(target, (ast.List, ast.Tuple)):
        return any(_target_binds_all(element) for element in target.elts)
    return False
def _unpack_target_value_pairs(
        targets: list[ast.expr], values: list[ast.expr],
) -> list[tuple[ast.expr, ast.expr]] | None:
    starred = [index for index, target in enumerate(targets)
               if isinstance(target, ast.Starred)]
    if not starred:
        return (list(zip(targets, values, strict=True))
                if len(targets) == len(values) else None)
    if len(starred) != 1 or len(values) < len(targets) - 1:
        return None
    star_index = starred[0]
    tail_count = len(targets) - star_index - 1
    middle_end = len(values) - tail_count
    starred_value = ast.List(
        elts=list(values[star_index:middle_end]), ctx=ast.Load(),
    )
    pairs = list(zip(
        targets[:star_index], values[:star_index], strict=True,
    ))
    pairs.append((targets[star_index].value, starred_value))
    if tail_count:
        pairs.extend(zip(
            targets[star_index + 1:], values[middle_end:], strict=True,
        ))
    return pairs
def _target_all_value(
        target: ast.expr, value: ast.expr,
) -> tuple[bool, ast.expr | None]:
    if is_all_name_target(target):
        return True, value
    if isinstance(target, ast.Starred):
        return _target_all_value(target.value, value)
    if not isinstance(target, (ast.List, ast.Tuple)):
        return False, None
    if not isinstance(value, (ast.List, ast.Tuple)):
        return _target_binds_all(target), None
    pairs = _unpack_target_value_pairs(target.elts, value.elts)
    if pairs is None:
        return _target_binds_all(target), None
    found = False
    selected_value: ast.expr | None = None
    for child_target, child_value in pairs:
        bound, selected = _target_all_value(child_target, child_value)
        if bound:
            found = True
            selected_value = selected
    return found, selected_value
def _assignment_all_value(
        stmt: ast.Assign | ast.AnnAssign,
) -> tuple[bool, ast.expr | None]:
    if isinstance(stmt, ast.AnnAssign):
        if stmt.value is not None and is_all_name_target(stmt.target):
            return True, stmt.value
        return False, None
    found = False
    selected_value: ast.expr | None = None
    for target in stmt.targets:
        bound, value = _target_all_value(target, stmt.value)
        if bound:
            found = True
            selected_value = value
    return found, selected_value
def binds_all_name(stmt: ast.stmt) -> bool:
    if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
        return _assignment_all_value(stmt)[0]
    if isinstance(stmt, (ast.Import, ast.ImportFrom)):
        return any((a.asname or a.name.split(".")[0]) == "__all__"
                   for a in stmt.names)
    return is_all_walrus_stmt(stmt)
def _lambda_shadow_tasks(cur: ast.Lambda,
                         shadowed: frozenset[str]) -> list[tuple[ast.AST, frozenset[str]]]:
    tasks: list[tuple[ast.AST, frozenset[str]]] = [
        (_d, shadowed) for _d in list(cur.args.defaults) + [
            _d for _d in cur.args.kw_defaults if _d is not None]]
    inner = set(shadowed)
    inner.update(a.arg for a in cur.args.posonlyargs
                 + cur.args.args + cur.args.kwonlyargs)
    if cur.args.vararg:
        inner.add(cur.args.vararg.arg)
    if cur.args.kwarg:
        inner.add(cur.args.kwarg.arg)
    tasks.append((cur.body, frozenset(inner)))
    return tasks
def _comp_shadow_tasks(cur: ast.AST,
                       shadowed: frozenset[str]) -> list[tuple[ast.AST, frozenset[str]]]:
    tasks: list[tuple[ast.AST, frozenset[str]]] = []
    inner = set(shadowed)
    for gen in cur.generators:
        tasks.append((gen.iter, frozenset(inner)))
        inner.update(iter_unpack_target_names(gen.target))
        for cond in gen.ifs:
            tasks.append((cond, frozenset(inner)))
    final = frozenset(inner)
    if isinstance(cur, ast.DictComp):
        tasks.append((cur.key, final))
        tasks.append((cur.value, final))
    else:
        tasks.append((cur.elt, final))
    return tasks
def is_all_self_ref_rebind(value: ast.expr) -> bool:
    stack: list[tuple[ast.AST, frozenset[str]]] = [(value, frozenset())]
    while stack:
        cur, _sh = stack.pop()
        if isinstance(cur, ast.Name):
            if (cur.id == "__all__" and "__all__" not in _sh
                    and isinstance(cur.ctx, ast.Load)):
                return True
            continue
        if isinstance(cur, ast.Lambda):
            stack.extend(reversed(_lambda_shadow_tasks(cur, _sh)))
            continue
        if isinstance(cur, (ast.ListComp, ast.SetComp, ast.GeneratorExp,
                            ast.DictComp)):
            stack.extend(reversed(_comp_shadow_tasks(cur, _sh)))
            continue
        for _child in ast.iter_child_nodes(cur):
            stack.append((_child, _sh))
    return False
def _str_element(e: ast.expr) -> list[str]:
    _value = str_constant_value(e)
    if _value is not None:
        return [_value]
    if isinstance(e, ast.Starred):
        return _str_elements(e.value)
    return []
def _is_repeatable_sequence_node(value: ast.expr) -> bool:
    return (isinstance(value, (ast.List, ast.Tuple))
            or (isinstance(value, ast.BinOp)
                and isinstance(value.op, (ast.Add, ast.Mult))))
def _sequence_repeat_operands(value: ast.BinOp) -> tuple[ast.expr, int] | None:
    for seq_node, times_node in ((value.left, value.right),
                                 (value.right, value.left)):
        if not _is_repeatable_sequence_node(seq_node):
            continue
        times = _signed_int_constant(times_node)
        if times is not None:
            return seq_node, times
    return None
def _flatten_add_chain(value: ast.expr) -> list[ast.expr]:
    _ops: list[ast.expr] = []
    _n: ast.expr = value
    while isinstance(_n, ast.BinOp) and isinstance(_n.op, ast.Add):
        _ops.append(_n.right)
        _n = _n.left
    _ops.append(_n)
    _ops.reverse()
    return _ops
def _str_elements(value: ast.expr) -> list[str]:
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return [s for e in value.elts for s in _str_element(e)]
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
        return [s for o in _flatten_add_chain(value) for s in _str_elements(o)]
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Mult):
        operands = _sequence_repeat_operands(value)
        if operands is None:
            return []
        seq_node, times = operands
        return _str_elements(seq_node) * times if times > 0 else []
    return []
def _is_all_load_name(node: ast.expr) -> bool:
    return (isinstance(node, ast.Name) and node.id == "__all__"
            and isinstance(node.ctx, ast.Load))
def _expand_seq_items(items: list[ast.expr], base: list[str]) -> list[str]:
    expanded: list[str] = []
    for item in items:
        if isinstance(item, ast.Starred):
            expanded.extend(_all_seq_value(item.value, base))
            continue
        expanded.extend(_str_element(item))
    return expanded
def _int_constant(node: ast.expr) -> int | None:
    if (isinstance(node, ast.Constant) and isinstance(node.value, int)
            and not isinstance(node.value, bool)):
        return node.value
    return None
def _signed_int_constant(node: ast.expr) -> int | None:
    _sign = 1
    while isinstance(node, ast.UnaryOp) and isinstance(
            node.op, (ast.UAdd, ast.USub)):
        if isinstance(node.op, ast.USub):
            _sign = -_sign
        node = node.operand
    value = _int_constant(node)
    return None if value is None else _sign * value
def _repeat_all_value(value: ast.BinOp, base: list[str]) -> list[str]:
    self_ref = _is_self_ref_rebind_safe(value)
    for seq_node, times_node in ((value.left, value.right),
                                 (value.right, value.left)):
        if not (_is_all_load_name(seq_node)
                or _is_repeatable_sequence_node(seq_node)):
            continue
        times = _signed_int_constant(times_node)
        if times is None:
            return list(base) if self_ref else []
        seq = (list(base) if _is_all_load_name(seq_node)
               else _all_seq_value(seq_node, base))
        return seq * times if times > 0 else []
    return list(base) if self_ref else []
def _all_seq_value(value: ast.expr, base: list[str]) -> list[str]:
    if _is_all_load_name(value):
        return list(base)
    if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
            and value.func.id in {"list", "tuple"} and not value.keywords
            and len(value.args) == 1):
        return _all_seq_value(value.args[0], base)
    if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
        return _expand_seq_items(value.elts, base)
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Add):
        return [name for part in _flatten_add_chain(value)
                for name in _all_seq_value(part, base)]
    if isinstance(value, ast.BinOp) and isinstance(value.op, ast.Mult):
        return _repeat_all_value(value, base)
    return []
def _is_self_ref_rebind_safe(value: ast.expr) -> bool:
    try:
        return is_all_self_ref_rebind(value)
    except RecursionError as _e:
        log_swallowed(__name__, _e,
                      context='_is_self_ref_rebind_safe:RecursionError')
        return False
def _clamped_index(_idx: int, length: int) -> int:
    if _idx < 0:
        return max(_idx + length, 0)
    return min(_idx, length)
def _apply_all_append(current: list[str], args: list[ast.expr]) -> list[str]:
    _name = str_constant_value(args[0]) if args else None
    return current if _name is None else current + [_name]
def _apply_all_extend(current: list[str], args: list[ast.expr]) -> list[str]:
    return current + _all_seq_value(args[0], current) if args else current
def _apply_all_insert(current: list[str], args: list[ast.expr]) -> list[str]:
    if len(args) < 2:
        return current
    _idx = _signed_int_constant(args[0])
    _name = str_constant_value(args[1])
    if _idx is None or _name is None:
        return current
    _pos = _clamped_index(_idx, len(current))
    return current[:_pos] + [_name] + current[_pos:]
def _apply_all_pop(current: list[str], args: list[ast.expr]) -> list[str]:
    if not current:
        return current
    _idx = -1 if not args else _signed_int_constant(args[0])
    if _idx is None:
        return current
    if _idx < 0:
        _idx += len(current)
    if not 0 <= _idx < len(current):
        return current
    return current[:_idx] + current[_idx + 1:]
def _apply_all_remove(current: list[str], args: list[ast.expr]) -> list[str]:
    if len(args) != 1:
        return current
    _name = str_constant_value(args[0])
    if _name is None or _name not in current:
        return current
    _pos = current.index(_name)
    return current[:_pos] + current[_pos + 1:]
def _apply_all_clear(current: list[str], args: list[ast.expr]) -> list[str]:
    return current if args else []
def _all_item_assign_parts(
        node: ast.Assign | ast.AnnAssign,
) -> tuple[ast.expr, ast.expr] | None:
    if isinstance(node, ast.Assign):
        if len(node.targets) != 1:
            return None
        target, value = node.targets[0], node.value
    else:
        target, value = node.target, node.value
    if value is None or not isinstance(target, ast.Subscript):
        return None
    if not _is_all_load_name(target.value):
        return None
    return target.slice, value
def _literal_slice(node: ast.Slice) -> slice | None:
    bounds: list[int | None] = []
    for part in (node.lower, node.upper, node.step):
        if part is None:
            bounds.append(None)
            continue
        value = _signed_int_constant(part)
        if value is None:
            return None
        bounds.append(value)
    if bounds[2] == 0:
        return None
    return slice(bounds[0], bounds[1], bounds[2])
def _literal_str_sequence(node: ast.expr) -> list[str] | None:
    if not isinstance(node, (ast.List, ast.Tuple)):
        return None
    names: list[str] = []
    for element in node.elts:
        name = str_constant_value(element)
        if name is None:
            return None
        names.append(name)
    return names
def _apply_all_slice_assign(current: list[str], slice_node: ast.Slice,
                            value: ast.expr) -> list[str]:
    selector = _literal_slice(slice_node)
    replacement = _literal_str_sequence(value)
    if selector is None or replacement is None:
        return current
    updated = list(current)
    try:
        updated[selector] = replacement
    except ValueError:  # jwsgj:silent-ok
        return current
    return updated
def _apply_all_item_assign(
        node: ast.Assign | ast.AnnAssign, current: list[str]) -> list[str]:
    parts = _all_item_assign_parts(node)
    if parts is None:
        return current
    subscript, value = parts
    if isinstance(subscript, ast.Slice):
        return _apply_all_slice_assign(current, subscript, value)
    index = _signed_int_constant(subscript)
    name = str_constant_value(value)
    if index is None or name is None:
        return current
    if index < 0:
        index += len(current)
    if not 0 <= index < len(current):
        return current
    return current[:index] + [name] + current[index + 1:]
def _apply_all_delete_items(node: ast.Delete,
                            current: list[str]) -> list[str]:
    updated = list(current)
    for target in node.targets:
        if (not isinstance(target, ast.Subscript)
                or not _is_all_load_name(target.value)):
            continue
        if not isinstance(target.slice, ast.Slice):
            updated = _apply_all_pop(updated, [target.slice])
            continue
        selector = _literal_slice(target.slice)
        if selector is not None:
            del updated[selector]
    return updated
_ALL_METHOD_MUTATORS: dict[str, Callable[[list[str], list[ast.expr]],
                                         list[str]]] = {
    "append": _apply_all_append,
    "extend": _apply_all_extend,
    "insert": _apply_all_insert,
    "pop": _apply_all_pop,
    "remove": _apply_all_remove,
    "clear": _apply_all_clear,
}
ALL_MUTATOR_METHODS: frozenset[str] = frozenset(_ALL_METHOD_MUTATORS)
def _is_all_method_call(call: ast.Call) -> bool:
    func = call.func
    return (
        isinstance(func, ast.Attribute)
        and func.attr in _ALL_METHOD_MUTATORS
        and isinstance(func.value, ast.Name)
        and func.value.id == "__all__"
        and not call.keywords
    )
def _apply_all_method_stmt(call: ast.Call,
                           current: list[str]) -> list[str]:
    if not _is_all_method_call(call):
        return current
    return _ALL_METHOD_MUTATORS[call.func.attr](current, call.args)
def _apply_all_value(value: ast.expr, current: list[str]) -> list[str]:
    if _is_self_ref_rebind_safe(value):
        return _all_seq_value(value, current)
    return _str_elements(value)
def _augassign_targets_all(node: ast.AugAssign) -> bool:
    return is_all_name_target(node.target)
def _apply_all_augop(node: ast.AugAssign, current: list[str]) -> list[str]:
    if isinstance(node.op, ast.Add):
        return current + _all_seq_value(node.value, current)
    if isinstance(node.op, ast.Sub):
        removed = set(_str_elements(node.value))
        return [name for name in current if name not in removed]
    _times = _signed_int_constant(node.value)
    if isinstance(node.op, ast.Mult) and _times is not None:
        return current * _times
    return current
def _is_scope_call_expr(node: ast.AST) -> bool:
    return (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Call))
def _advance_assign_value(node: ast.Assign | ast.AnnAssign,
                          current: list[str]) -> list[str]:
    _, value = _assignment_all_value(node)
    return [] if value is None else _apply_all_value(value, current)
def _advance_reset_value(node: ast.AST, current: list[str]) -> list[str]:
    return []
def _advance_walrus_value(node: ast.Expr, current: list[str]) -> list[str]:
    return _apply_all_value(node.value.value, current)
_ALL_STEP_RULES: tuple[tuple[type, Callable[[ast.AST], bool],
                              Callable[[ast.AST, list[str]], list[str]]], ...] = (
    (ast.Assign, binds_all_name, _advance_assign_value),
    (ast.AnnAssign, binds_all_name, _advance_assign_value),
    (ast.AugAssign, _augassign_targets_all, _apply_all_augop),
    (ast.Import, binds_all_name, _advance_reset_value),
    (ast.ImportFrom, binds_all_name, _advance_reset_value),
    (ast.Expr, is_all_walrus_stmt, _advance_walrus_value),
)
def _all_step_result(node: ast.AST,
                     current: list[str]) -> tuple[bool, list[str]]:
    if (isinstance(node, (ast.Assign, ast.AnnAssign))
            and _all_item_assign_parts(node) is not None):
        return False, _apply_all_item_assign(node, current)
    for node_type, eligible, advance in _ALL_STEP_RULES:
        if isinstance(node, node_type) and eligible(node):
            return True, advance(node, current)
    if _is_scope_call_expr(node):
        return False, _apply_all_method_stmt(node.value, current)
    return False, current
def is_all_delete(node: ast.AST) -> bool:
    return (isinstance(node, ast.Delete)
            and any(_target_binds_all(t) for t in node.targets))
def _static_all_branch(node: ast.If) -> list[ast.stmt] | None:
    if isinstance(node.test, ast.Constant):
        return node.body if bool(node.test.value) else node.orelse
    polarity = main_guard_branch(node.test)
    if polarity is not None:
        return node.orelse if polarity else node.body
    if is_main_check(node.test):
        return node.orelse
    return None

def _merge_all_branch_outcomes(
        outcomes: list[tuple[bool, list[str]]]) -> tuple[bool, list[str]]:
    bound = any(item_bound for item_bound, _ in outcomes)
    names: list[str] = []
    for _, current in outcomes:
        for name in current:
            if name not in names:
                names.append(name)
    return bound, names

def _advance_all_statement_list(
        body: list[ast.stmt], bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    for node in body:
        bound, current = _advance_all_statement(node, bound, current)
    return bound, current

def _advance_all_try(
        node: ast.AST, bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    prefix_outcomes = [(bound, list(current))]
    body_bound, body_current = bound, list(current)
    for statement in node.body:
        body_bound, body_current = _advance_all_statement(
            statement, body_bound, body_current)
        prefix_outcomes.append((body_bound, list(body_current)))
    outcomes = [
        _advance_all_statement_list(node.orelse, body_bound, body_current)
    ]
    for handler in node.handlers:
        for prefix_bound, prefix_current in prefix_outcomes:
            outcomes.append(_advance_all_statement_list(
                handler.body, prefix_bound, prefix_current))
    if node.finalbody:
        outcomes = [
            _advance_all_statement_list(node.finalbody, item_bound, item_current)
            for item_bound, item_current in outcomes
        ]
    return _merge_all_branch_outcomes(outcomes)

def _advance_all_loop(
        node: ast.For | ast.AsyncFor | ast.While, bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    body_outcome = _advance_all_statement_list(node.body, bound, list(current))
    outcomes = [body_outcome]
    if node.orelse:
        outcomes.extend((
            _advance_all_statement_list(node.orelse, bound, list(current)),
            _advance_all_statement_list(node.orelse, *body_outcome),
        ))
    else:
        outcomes.append((bound, list(current)))
    return _merge_all_branch_outcomes(outcomes)

def _match_case_is_irrefutable(case: ast.match_case) -> bool:
    return (case.guard is None and isinstance(case.pattern, ast.MatchAs)
            and case.pattern.pattern is None)

def _advance_all_match(
        node: ast.Match, bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    outcomes = [
        _advance_all_statement_list(case.body, bound, list(current))
        for case in node.cases
    ]
    if not any(_match_case_is_irrefutable(case) for case in node.cases):
        outcomes.insert(0, (bound, list(current)))
    return _merge_all_branch_outcomes(outcomes)

def _advance_all_container(
        container: ast.AST, bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    for _is_stmts, items in _scope_field_lists(container):
        for item in items:
            if isinstance(item, ast.stmt):
                bound, current = _advance_all_statement(item, bound, current)
            else:
                bound, current = _advance_all_container(item, bound, current)
    return bound, current

def _advance_all_statement(
        node: ast.stmt, bound: bool,
        current: list[str]) -> tuple[bool, list[str]]:
    if is_all_delete(node):
        return False, []
    if isinstance(node, ast.Delete):
        return bound, _apply_all_delete_items(node, current)
    step_bound, current = _all_step_result(node, current)
    bound = bound or step_bound
    if isinstance(node, ast.If):
        static_branch = _static_all_branch(node)
        if static_branch is not None:
            return _advance_all_statement_list(static_branch, bound, current)
        outcomes = [
            _advance_all_statement_list(branch, bound, list(current))
            for branch in (node.body, node.orelse)
        ]
        return _merge_all_branch_outcomes(outcomes)
    if isinstance(node, TRY_NODE_TYPES):
        return _advance_all_try(node, bound, current)
    if isinstance(node, (ast.For, ast.AsyncFor, ast.While)):
        return _advance_all_loop(node, bound, current)
    if isinstance(node, ast.Match):
        return _advance_all_match(node, bound, current)
    if isinstance(node, BLOCK_CONTAINER_NODES):
        return _advance_all_container(node, bound, current)
    return bound, current

def parse_all(tree: ast.Module) -> tuple[bool, list[str]]:
    bound, current = _advance_all_statement_list(tree.body, False, [])
    if not bound:
        return False, []
    return True, current
def _count_decorators(decorator_list: list[ast.expr],
                      decorator_usage: Counter) -> None:
    for d in decorator_list:
        d_name = _safe_unparse(d).split("(")[0]
        if d_name:
            decorator_usage[d_name] += 1
def _collect_fn_key_entities(node: ast.FunctionDef | ast.AsyncFunctionDef,
                             public_api: list[str], entry_points: list[str],
                             decorator_usage: Counter) -> None:
    name = node.name
    if not name.startswith("_"):
        public_api.append(name)
    if name.startswith("run_") or name == "main":
        entry_points.append(name)
    _count_decorators(node.decorator_list, decorator_usage)
def _collect_class_key_entities(node: ast.ClassDef, public_api: list[str],
                                exception_classes: list[str],
                                decorator_usage: Counter) -> None:
    name = node.name
    if not name.startswith("_"):
        public_api.append(name)
    base_names = [_safe_unparse(b) for b in node.bases]
    if (any("Error" in b or "Exception" in b for b in base_names)
            or name.endswith(("Error", "Exception"))):
        exception_classes.append(name)
    _count_decorators(node.decorator_list, decorator_usage)
def _collect_config_key_entries(node: ast.Assign | ast.AnnAssign,
                                config_entries: list[str]) -> None:
    if isinstance(node, ast.Assign):
        targets = node.targets
    elif node.value is not None:
        targets = [node.target]
    else:
        return
    for target in targets:
        for name in iter_unpack_target_names(target):
            if name.isupper() and len(name) > 2:
                config_entries.append(name)
_RULE_SYMBOL_PREFIXES = ("RULE_", "RULES_", "CHECK_", "CHECKS_",
                         "DETECTOR_", "PATTERN_", "POLICY_", "LINT_")
_RULE_SYMBOL_SUFFIXES = ("_RULE", "_RULES", "_RULE_ID", "_CHECK")
def _unique_names(names: list[str]) -> list[str]:
    return list(dict.fromkeys(names))
def _is_rule_symbol(name: str) -> bool:
    text = name.lstrip("_")
    upper = text.upper()
    return (upper.startswith(_RULE_SYMBOL_PREFIXES)
            or upper.endswith(_RULE_SYMBOL_SUFFIXES)
            or "规则" in text)
def extract_key_entities(tree: ast.Module, rel_path: str,
                          all_symbols: list[str]) -> FileKeyEntities:
    public_api: list[str] = []
    exception_classes: list[str] = []
    config_entries: list[str] = []
    entry_points: list[str] = []
    decorator_usage: Counter = Counter()
    for node in iter_scope_stmts(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            _collect_fn_key_entities(node, public_api, entry_points,
                                     decorator_usage)
            continue
        if isinstance(node, ast.ClassDef):
            _collect_class_key_entities(node, public_api,
                                        exception_classes, decorator_usage)
            continue
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            _collect_config_key_entries(node, config_entries)
    registered_rules = _unique_names([s for s in all_symbols
                                      if _is_rule_symbol(s)])
    return FileKeyEntities(
        filepath=rel_path,
        public_api=_unique_names(public_api),
        exported_symbols=list(all_symbols),
        exception_classes=_unique_names(exception_classes),
        config_entries=_unique_names(config_entries),
        entry_points=_unique_names(entry_points),
        registered_rules=registered_rules,
        decorator_usage=dict(decorator_usage),
    )

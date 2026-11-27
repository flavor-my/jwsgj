from __future__ import annotations  # noqa: I001
import ast
import builtins
import keyword
import logging
import os
import re
import sys
from collections import Counter
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from jwsgj.build_text_scoring import (
    DOMAIN_HINT_TO_TYPE_KEY,
    DOMAIN_NEGATIVES,
    md_escape_cell,
    resolve_domain_key,
)
from jwsgj.diag_shared_ast_surface import (
    collect_module_symbols,
    first_line,
)
from jwsgj.diag_shared_source_core import (
    count_lines,
    decode_source_bytes,
    read_source,
    read_source_strict,
)
from jwsgj.diag_smell_detector import CPGSmellAnalyzer, SmellInstance
from jwsgj.diag_types_normalize import (
    clean_str_list,
    finite_float_or_none,
    int_metric,
)
from jwsgj.diag_types_vocab import (
    DEFAULT_VIRTUAL_FILENAME,
    FIELD_TOTAL_FUNCTIONS,
    PARSE_DEGRADE_EXC,
)
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import (
    is_archive_or_cache_path,
    is_test_dir_name,
    is_test_source_basename,
    prune_ignore_dirs,
    py_stem,
    safe_relpath,
    scan_exclude_dirs,
    scan_prune_dirs,
)
from jwsgj.skill_profile import detect_layout
_log = logging.getLogger(__name__)
_DEFAULT_MIN_CONFIDENCE = 0.0
_DEFAULT_SKILL_NAME = ""
_DEFAULT_SKILL_TYPE = "generic"
_BUILTIN_NAMES = frozenset(dir(builtins))
__all__ = [
    'CATEGORY_SCENARIOS',
    'IO_PATTERNS',
    'SQL_PATTERNS',
    'all_capabilities',
    'analyze_smells',
    'as_lower_text',
    'entity_name',
    'entity_names',
    'infer_key_capabilities',
    'infer_module_category',
    'infer_module_purpose',
    'match_capability_labels',
    'module_stem',
    'norm_entity_list',
    'norm_text',
    'normalize_rel_path',
    'normalize_scan_modules',
    'one_line',
    'profile_directory',
    'profile_file',
    'render_capability_boundary',
    'render_forced_workflow_constraints',
    'render_full_module_capabilities',
    'render_module_capability_table',
    'render_module_responsibility_list',
    'render_scan_summary',
    'render_trigger_entrypoint_mapping',
    'scan_file_manifest',
    'scan_full_analysis_files',
    'scan_skill_modules',
    'select_entry_func',
    'skill_label',
    'summarize_sql_by_dir',
]
def _coerce_path_text(value: Any) -> str:
    if isinstance(value, (str, bytes, os.PathLike)):
        try:
            return os.fsdecode(value)
        except (TypeError, ValueError, OSError) as exc:
            log_swallowed(__name__, exc,
                          context=f'_coerce_path_text:{type(exc).__name__}')
            return ""
    return ""
def _coerce_scan_root(value: Any) -> str:
    text = _coerce_path_text(value)
    return text if text.strip() else ""
def _require_scan_root(value: Any, api: str, *,
                       missing_exc: type[Exception] = ValueError) -> Path:
    root_text = _coerce_scan_root(value)
    if not root_text:
        raise missing_exc(f"{api}: 技能目录为空或类型非法: {value!r}")
    root = Path(root_text)
    if not root.is_dir():
        raise missing_exc(f"{api}: 技能目录不存在: {root_text}")
    return root
def all_capabilities(scan: dict) -> list:
    return [cap for mod in normalize_scan_modules(scan)
            for cap in clean_str_list(mod.get("key_capabilities"))]
def as_lower_text(value) -> str:
    return str(value or "").lower()
_PREFIX_MAP = {
    "核心引擎": ["core_", "engine_", "hub_"],
    "流程编排": ["pipeline_", "orchestrat_", "flow_"],
    "检测/诊断": ["diag_", "detect_", "scan_", "inspect_", "lint_"],
    "修复/清理": ["fix_", "repair_", "heal_", "refactor_"],
    "构建/生成": ["build_", "create_", "generate_", "scaffold_"],
    "安全/守卫": ["guard_", "gate_", "safe_", "security_"],
    "类型/数据模型": ["types_", "schema_", "proto_"],
    "工具/辅助": ["utils_", "helper_", "tool_", "common_"],
    "测试": ["test_", "mock_", "fixture_"],
    "诊断/分析": ["diagnos_", "graph_"],
    "可发现性/优化": ["discover_", "trigger_", "optim_"],
    "脚本/执行": ["script_", "cli_", "exec_"],
    "上下文/约束": ["context_", "contract_", "constraint_"],
    "交叉验证": ["xv_"],
    "治疗/反馈": ["retrospective_"],
    "生命周期/健康": ["lifecycle_", "health_", "maturity_", "coverage_"],
    "清理/共存": ["cleaner_"],
    "报告/可视化": ["html_", "report_"],
    "适配/项目": ["project_", "adapter_"],
    "前置介入": ["pre_creation_", "preintervention_"],
}
_SUBSTRING_RULES = [
    (["coexistence"], "清理/共存"),
    (["dedup", "overlap"], "清理/共存"),
    (["treatment", "feedback", "outcome"], "治疗/反馈"),
    (["maintain", "hygiene", "consistency"], "维护/巡检"),
    (["antipattern", "code_smell", "bad_smell"], "检测/诊断"),
    (["core", "engine", "hub"], "核心引擎"),
    (["pipeline", "stage", "phase", "flow", "orchestrat"], "流程编排"),
    (["diag", "detect", "scan", "inspect", "lint"], "检测/诊断"),
    (["check"], "检测/诊断"),
    (["health"], "生命周期/健康"),
    (["cleaner"], "清理/共存"),
    (["fix", "repair", "heal", "clean", "refactor"], "修复/清理"),
    (["build", "create", "generate", "init", "scaffold"], "构建/生成"),
    (["guard", "gate", "safe", "security", "protect"], "安全/守卫"),
    (["types", "model", "schema", "proto", "dataclass"], "类型/数据模型"),
    (["utils", "helper", "tool", "common", "misc"], "工具/辅助"),
    (["test", "mock", "fixture"], "测试"),
    (["diagnos", "graph", "call", "trace"], "诊断/分析"),
    (["discover", "trigger", "optim", "search"], "可发现性/优化"),
    (["script", "cli", "exec", "run"], "脚本/执行"),
    (["context", "contract", "constraint"], "上下文/约束"),
    (["xv", "cross_valid", "crossvalid"], "交叉验证"),
    (["retrospective"], "治疗/反馈"),
    (["maturity", "coverage", "lifecycle"], "生命周期/健康"),
    (["html", "report"], "报告/可视化"),
    (["project", "adapter"], "适配/项目"),
    (["pre_creation", "preintervention"], "前置介入"),
    (["business", "exception", "simulate", "codegen", "verify", "rules", "scoring", "scorer"], "检测/诊断"),
    (["lazy"], "基础设施"),
    (["analysis"], "诊断/分析"),
]
_DOCSTRING_RULES = [
    (["诊断", "diag", "检测"], "检测/诊断"),
    (["修复", "fix"], "修复/清理"),
    (["维护", "maintain", "巡检"], "维护/巡检"),
    (["交叉验证", "cross valid"], "交叉验证"),
    (["复盘", "retrospective"], "治疗/反馈"),
    (["清理", "共存", "clean"], "清理/共存"),
    (["健康", "生命周期", "health"], "生命周期/健康"),
    (["报告", "report", "html"], "报告/可视化"),
    (["适配", "adapter", "项目"], "适配/项目"),
    (["安全", "security", "漏洞"], "安全/守卫"),
    (["可发现性", "触发", "discover"], "可发现性/优化"),
    (["重构", "refactor"], "修复/清理"),
    (["契约", "contract", "约束"], "上下文/约束"),
    (["治疗", "treatment"], "治疗/反馈"),
    (["反哺", "feedback"], "治疗/反馈"),
    (["前置介入", "pre creation", "预介入"], "前置介入"),
]
_CAT_PURPOSE = {
    "交叉验证": "交叉验证：多源结果的一致性核对与冲突定位",
    "治疗/反馈": "治疗/反馈：问题处置与反馈闭环",
    "生命周期/健康": "生命周期/健康：健康评分与成熟度评估",
    "清理/共存": "清理/共存：新旧实现的共存判定与安全清理",
    "报告/可视化": "报告/可视化：结果的可视化呈现",
    "适配/项目": "适配/项目：多项目形态的适配与配置加载",
    "前置介入": "前置介入：创建前置质量检查",
    "基础设施": "基础设施：模块加载与导入等基础能力",
}
_NAME_CAP_MAP = {
    "diag": "代码诊断", "detect": "问题检测", "scan": "扫描",
    "fix": "自动修复", "clean": "代码清理", "refactor": "重构",
    "build": "构建", "create": "创建", "generate": "生成",
    "guard": "安全守卫", "gate": "门禁检查",
    "graph": "调用图分析",
    "pipeline": "流水线编排", "stage": "阶段执行",
    "score": "质量评分", "test": "测试",
    "discover": "可发现性", "trigger": "触发优化",
    "script": "脚本管理", "exec": "执行",
    "context": "上下文管理", "contract": "契约约束",
    "types": "类型定义", "utils": "工具函数",
    "maintain": "维护巡检", "health": "健康检查",
    "consistency": "一致性检查", "hygiene": "代码卫生",
    "xv": "交叉验证", "cross_valid": "交叉验证",
    "treatment": "治疗实施", "retrospective": "复盘反哺",
    "feedback": "反馈闭环", "coordinator": "反馈协调",
    "coexistence": "共存检测", "cleaner": "代码清理",
    "verifier": "安全验证",
    "dedup": "去重合并", "overlap": "重叠检测",
    "lifecycle": "生命周期管理", "snapshot": "快照管理",
    "maturity": "成熟度评估", "coverage": "覆盖分析",
    "html": "可视化报告", "report": "报告生成",
    "project": "项目适配", "adapter": "项目适配",
    "pre_creation": "前置介入", "preintervention": "前置介入",
    "security": "安全审计", "taint": "污点追踪",
    "business": "业务诊断", "exception": "异常分析",
    "simulate": "模拟执行", "codegen": "代码生成",
    "verify": "结果验证", "rules": "规则匹配",
    "scoring": "质量评分", "scorer": "评分引擎",
    "lazy": "延迟导入", "analysis": "分析总线",
    "callgraph": "调用图分析",
    "blindspot": "盲点扫描",
    "orchestrate": "流程编排",
    "constraint": "约束引擎",
    "evolution": "进化定律", "rollback": "回滚管理",
    "template": "模板生成", "dependency": "依赖分析",
    "skill_doc": "技能文档", "matching": "匹配规则", "semantic": "语义匹配",
    "preflight": "预检",
    "factory": "工厂构建", "init": "初始化",
}
_FUNC_NAME_CAP_RULES = [
    (["scan", "detect", "find", "search"], "扫描检测"),
    (["fix", "repair", "heal", "resolve"], "自动修复"),
    (["build", "create", "generate", "make", "init"], "构建生成"),
    (["validate", "verify", "check", "guard"], "验证检查"),
    (["score", "rate", "evaluate", "measure"], "评分度量"),
    (["optimize", "enhance", "improve"], "优化增强"),
    (["clean", "remove", "delete", "purge"], "清理移除"),
    (["retrospective", "review", "reflect"], "复盘反哺"),
    (["treatment", "treat", "cure"], "治疗实施"),
    (["xv", "cross_valid", "crossvalid", "arbitrate"], "交叉验证"),
    (["coexist", "dedup", "overlap"], "共存去重"),
    (["health", "lifecycle", "maturity", "coverage"], "健康治理"),
    (["report", "html", "render"], "可视化报告"),
    (["adapt", "project"], "项目适配"),
    (["security", "taint", "vulnerability"], "安全审计"),
    (["discover", "trigger", "attention"], "可发现性优化"),
    (["contract", "constraint", "invariant"], "契约约束"),
    (["rollback", "snapshot", "backup"], "回滚保护"),
]
_CAMEL_BOUNDARY_LOWER_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
_CAMEL_BOUNDARY_UPPER_RE = re.compile(r"(?<=[A-Z])(?=[A-Z][a-z])")
_TERM_START_RE_CACHE: dict[str, re.Pattern] = {}
def _split_identifier_words(text) -> str:
    value = text if isinstance(text, str) else str(text or "")
    value = _CAMEL_BOUNDARY_LOWER_RE.sub("_", value)
    value = _CAMEL_BOUNDARY_UPPER_RE.sub("_", value)
    return value.lower()
def _term_at_word_start(text: str, term: str) -> bool:
    if not term:
        return False
    term_lower = term.lower()
    pattern = _TERM_START_RE_CACHE.get(term_lower)
    if pattern is None:
        pattern = re.compile(
            r"(?<![a-z0-9])(?:re)?" + re.escape(term_lower))
        _TERM_START_RE_CACHE[term_lower] = pattern
    return bool(pattern.search(text))
def _match_keyword_category(text: str, rules: list) -> str | None:
    for keywords, cat in rules:
        if any(_term_at_word_start(text, kw) for kw in keywords):
            return cat
    return None
def _match_prefix_category(name_lower: str, prefix_map: dict) -> str | None:
    for cat, prefixes in prefix_map.items():
        for p in prefixes:
            if name_lower.startswith(p):
                return cat
    return None
def infer_module_category(name: str, doc: str) -> str:
    name_lower = as_lower_text(name)
    name_words = _split_identifier_words(name)
    doc_words = _split_identifier_words(doc)
    stem = module_stem(name_lower)
    if stem == '__init__':
        return "基础设施"
    if stem == '__main__':
        return "脚本/执行"
    cat = _match_prefix_category(name_lower, _PREFIX_MAP)
    if cat is not None:
        return cat
    cat = _match_keyword_category(name_words, _SUBSTRING_RULES)
    if cat is not None:
        return cat
    cat = _match_keyword_category(doc_words, _DOCSTRING_RULES)
    if cat is not None:
        return cat
    return "通用"
def entity_name(entity: Any) -> str:
    if not isinstance(entity, dict):
        return ""
    name = entity.get("name")
    return name if isinstance(name, str) and name else ""
def entity_names(items: list) -> list[str]:
    names = [entity_name(item) for item in norm_entity_list(items)]
    return [name for name in names if name]
def _fallback_module_purpose(name: str, doc: str, functions: list,
                             classes: list, exports: list) -> str:
    cat = infer_module_category(name, doc)
    if cat in _CAT_PURPOSE:
        return _CAT_PURPOSE[cat]
    main_exports = [e for e in norm_entity_list(exports)[:5]
                    if isinstance(e, str) and e]
    all_names = (main_exports + entity_names(functions)[:5]
                 + entity_names(classes)[:3])
    if all_names:
        return f"提供: {', '.join(all_names[:6])}"
    return ""
def infer_module_purpose(name: str, doc: str, functions: list,
                          classes: list, exports: list) -> str:
    if not isinstance(doc, str):
        doc = ""
    if doc:
        doc_first = first_line(doc)
        if doc_first and len(doc_first) >= 3:
            return doc_first[:120]
    return _fallback_module_purpose(name, doc, functions, classes, exports)
def match_capability_labels(all_names: list, rules: list) -> set[str]:
    labels: set[str] = set()
    for name in norm_entity_list(all_names):
        words_text = _split_identifier_words(name)
        for verbs, label in rules:
            terms = (verbs,) if isinstance(verbs, str) else verbs
            if any(_term_at_word_start(words_text, term) for term in terms):
                labels.add(label)
    return labels
def infer_key_capabilities(name: str, functions: list, classes: list) -> list:
    name_caps: list[str] = []
    name_words = _split_identifier_words(name)
    for kw, cap in _NAME_CAP_MAP.items():
        if _term_at_word_start(name_words, kw) and cap not in name_caps:
            name_caps.append(cap)
    entity_caps = match_capability_labels(
        entity_names(functions) + entity_names(classes),
        _FUNC_NAME_CAP_RULES)
    ordered = name_caps + [cap for cap in sorted(entity_caps)
                           if cap not in name_caps]
    return ordered[:8]
def norm_text(value: Any, default: str = "") -> str:
    if isinstance(value, str):
        return value
    return default
def normalize_rel_path(path: str) -> str:
    return str(path or "").replace("\\", "/")
def module_stem(path: Any) -> str:
    basename = normalize_rel_path(_coerce_path_text(path)).rsplit("/", 1)[-1]
    return py_stem(basename)
def _resolve_package_layout(root: Path) -> tuple[str, tuple[str, ...]]:
    layout = detect_layout(root)
    root_name = layout.package_name
    if not (root_name.isidentifier() and not keyword.iskeyword(root_name)):
        return "", ()
    if not layout.package_root or not layout.root:
        return root_name, ()
    try:
        prefix = Path(layout.package_root).relative_to(layout.root).parts
    except ValueError:
        return root_name, ()
    return root_name, tuple(prefix)
def _resolve_scannable_rel_parts(py_file: Path, root: Path,
                                 exclude_lower: frozenset[str]) -> tuple | None:
    try:
        rel_parts = py_file.relative_to(root).parts
    except ValueError as e:
        _log.debug("路径计算失败（跳过）: %s: %s", py_file, e)
        return None
    rel_path = "/".join(rel_parts)
    if (any(part.lower() in exclude_lower for part in rel_parts)
            or any(part.startswith(".") for part in rel_parts)
            or any(is_test_dir_name(part) for part in rel_parts[:-1])
            or is_test_source_basename(rel_parts[-1])
            or is_archive_or_cache_path(rel_path, root_dir=str(root))):
        return None
    return rel_parts
def _load_source(py_file: Path) -> str | None:
    source = read_source(str(py_file))
    if source is None:
        _log.warning("scan_skill_modules: 读取py文件失败,跳过 %s", py_file)
    return source
def _build_module_entry(py_file: Path, rel_parts: tuple, source: str,
                        tree: ast.Module, import_root: str,
                        import_prefix: tuple[str, ...]) -> tuple:
    lines_count = count_lines(source)
    doc = (ast.get_docstring(tree) or "").strip()
    doc_summary = first_line(doc)
    (functions, classes, exports,
     top_level_imports, internal_imports,
     module_constants) = collect_module_symbols(tree, import_root)
    category = infer_module_category(py_file.stem, doc)
    purpose = infer_module_purpose(
        py_file.stem, doc, functions, classes, exports)
    key_capabilities = infer_key_capabilities(py_file.stem, functions, classes)
    rel_path = "/".join(rel_parts)
    prefix_len = len(import_prefix)
    inside_package = (rel_parts[:prefix_len] == import_prefix
                      if prefix_len else bool(import_root))
    import_parts = rel_parts[prefix_len:] if inside_package else rel_parts
    import_name = _dotted_import_name("/".join(import_parts))
    if import_name is not None and inside_package:
        import_name = ".".join(
            part for part in (import_root, import_name) if part)
    entry = {
        "name": py_file.stem,
        "path": rel_path,
        "import_name": import_name,
        "doc": doc,
        "doc_summary": doc_summary,
        "lines": lines_count,
        "category": category,
        "purpose": purpose,
        "functions": functions,
        "classes": classes,
        "exports": exports,
        "imports": sorted(set(top_level_imports)),
        "internal_imports": sorted(set(internal_imports)),
        "key_capabilities": key_capabilities,
        "constants": module_constants,
    }
    counts = {
        "lines": lines_count,
        "functions": len(functions),
        "classes": len(classes),
        "constants": len(module_constants),
        "exports": len(exports),
    }
    return entry, counts
def _scan_one_module(py_file: Path, root: Path,
                     exclude_lower: frozenset[str], import_root: str,
                     import_prefix: tuple[str, ...]) -> tuple[dict, tuple] | None:
    rel_parts = _resolve_scannable_rel_parts(py_file, root, exclude_lower)
    if rel_parts is None:
        return None
    source = _load_source(py_file)
    if source is None:
        return None
    tree, parse_error = _parse_source(source, str(py_file))
    if tree is None:
        _log.warning("scan_skill_modules: 解析py文件失败,跳过 %s: %s",
                     py_file, parse_error)
        return None
    try:
        return _build_module_entry(py_file, rel_parts, source, tree,
                                   import_root, import_prefix)
    except Exception as e:  # noqa: BLE001
        _log.warning("scan_skill_modules: 模块画像失败,跳过 %s: %s",
                     py_file, e)
        return None
def _iter_python_files(root: Path,
                       exclude_dirs: Iterable[str] | None = None):
    excluded = {d.lower() for d in (exclude_dirs or ())
                if isinstance(d, str) and d}
    def _on_walk_error(err: OSError) -> None:
        _log.warning("python 文件枚举中断（保留已发现结果）: %s: %s", root, err)
    for dirpath, dirnames, filenames in os.walk(root, onerror=_on_walk_error):
        prune_ignore_dirs(dirnames, root_dir=root)
        dirnames[:] = [
            d for d in dirnames
            if not d.startswith(".") and d.lower() not in excluded
        ]
        dirnames.sort()
        for fname in sorted(filenames):
            if fname.startswith(".") or not fname.lower().endswith(".py"):
                continue
            yield Path(dirpath) / fname
def _collect_python_files(root: Path,
                          exclude_dirs: Iterable[str] | None = None) -> list:
    return sorted(_iter_python_files(root, exclude_dirs))
def _empty_scan_result() -> dict:
    return {
        "total_modules": 0,
        "total_lines": 0,
        FIELD_TOTAL_FUNCTIONS: 0,
        "total_classes": 0,
        "total_exports": 0,
        "total_constants": 0,
        "import_root": "",
        "modules": [],
    }
def _complete_flat_local_imports(modules: list[dict], import_root: str) -> None:
    if import_root:
        return
    module_names = {
        name for entry in modules
        if isinstance(name := entry.get("import_name"), str) and name
    }
    package_names = {
        entry["import_name"] for entry in modules
        if isinstance(entry.get("import_name"), str)
        and str(entry.get("path", "")).replace("\\", "/").rsplit("/", 1)[-1]
        == "__init__.py"
    }
    for entry in modules:
        internal = set(entry.get("internal_imports") or ())
        for imported in entry.get("imports") or ():
            if not isinstance(imported, str):
                continue
            if imported in module_names or any(
                    imported == package or imported.startswith(package + ".")
                    for package in package_names):
                internal.add(imported)
        entry["internal_imports"] = sorted(internal)
def scan_skill_modules(target_dir: str) -> dict:
    root_text = _coerce_scan_root(target_dir)
    if not root_text:
        _log.warning("scan_skill_modules: 目标目录为空或类型非法，返回空扫描结果: %r",
                     target_dir)
        return _empty_scan_result()
    root = Path(root_text)
    if not root.is_dir():
        _log.warning("scan_skill_modules: 目标不是目录，返回空扫描结果: %s",
                     root_text)
        return _empty_scan_result()
    import_root, import_prefix = _resolve_package_layout(root)
    modules = []
    totals: Counter = Counter()
    exclude_lower = frozenset(
        str(name).lower() for name in scan_exclude_dirs(root_text))
    for py_file in _collect_python_files(root, exclude_lower):
        scanned = _scan_one_module(
            py_file, root, exclude_lower, import_root, import_prefix)
        if scanned is None:
            continue
        entry, counts = scanned
        totals.update(counts)
        modules.append(entry)
    _complete_flat_local_imports(modules, import_root)
    result = _empty_scan_result()
    result.update({
        "total_modules": len(modules),
        "total_lines": totals["lines"],
        FIELD_TOTAL_FUNCTIONS: totals["functions"],
        "total_classes": totals["classes"],
        "total_exports": totals["exports"],
        "total_constants": totals["constants"],
        "import_root": import_root,
        "modules": modules,
    })
    return result
_DEFAULT_SMELL_CONFIDENCE = 1.0
def _smell_confidence(metrics: dict) -> float:
    raw = metrics.get("confidence")
    number = finite_float_or_none(raw)
    if number is not None:
        return number
    if raw is not None:
        _log.debug("_smell_entry: confidence 非数值 %r，按默认 %.1f 处理",
                   raw, _DEFAULT_SMELL_CONFIDENCE)
    return _DEFAULT_SMELL_CONFIDENCE
def _coerce_min_confidence(value: Any) -> float:
    if value is None:
        return _DEFAULT_MIN_CONFIDENCE
    number = finite_float_or_none(value)
    if number is None:
        _log.warning("analyze_smells: min_confidence 非数值 %r，按默认 %.1f 处理",
                     value, _DEFAULT_MIN_CONFIDENCE)
        return _DEFAULT_MIN_CONFIDENCE
    if number < 0.0:
        _log.warning("analyze_smells: min_confidence 为负 %r，按下限 0 处理",
                     value)
        return 0.0
    return number
def _smell_entry(sm: SmellInstance, fpath: Path) -> dict:
    metrics = dict(sm.metrics) if sm.metrics else {}
    entry = {
        "file": str(fpath),
        "smell_type": sm.smell_type,
        "severity": sm.severity.value if sm.severity is not None else None,
        "description": sm.description,
        "metrics": metrics,
        "suggestions": list(sm.suggestions) if sm.suggestions else [],
        "confidence": _smell_confidence(metrics),
    }
    if sm.region is not None:
        entry["start_line"] = sm.region.start_line
        entry["end_line"] = sm.region.end_line
    return entry
def _iter_smell_source_files(skill_dir: str):
    root = Path(skill_dir)
    root_text = str(root)
    for fpath in _iter_python_files(root, scan_exclude_dirs(root_text)):
        rel_path = safe_relpath(str(fpath), root_text)
        if is_archive_or_cache_path(rel_path, root_dir=root_text):
            continue
        yield fpath
def analyze_smells(
        skill_dir: str, min_confidence: float = _DEFAULT_MIN_CONFIDENCE,
) -> dict:
    root = _require_scan_root(skill_dir, "analyze_smells",
                              missing_exc=FileNotFoundError)
    results = []
    analyzer = CPGSmellAnalyzer()
    floor = _coerce_min_confidence(min_confidence)
    for fpath in _iter_smell_source_files(str(root)):
        try:
            code = read_source_strict(str(fpath))
            smells = analyzer.analyze(code, str(fpath))
        except (OSError, *PARSE_DEGRADE_EXC) as exc:
            _log.debug("analyze_smells: 跳过 %s: %s", fpath, exc)
            continue
        entries = (_smell_entry(smell, fpath) for smell in smells)
        results.extend(filter(
            lambda entry: entry["confidence"] >= floor, entries))
    return {"total": len(results), "smells": results}
_DB_CONNECT_OWNERS = (
    r"sqlite3|psycopg2?|pymysql|MySQLdb|mysql\.connector|cx_Oracle|oracledb"
    r"|pyodbc|asyncpg|aiosqlite|duckdb|asyncmy|aiomysql|engine"
)
SQL_PATTERNS = {
    "execute": r"\.execute\s*\(",
    "fetchone": r"\.fetchone\s*\(",
    "fetchall": r"\.fetchall\s*\(",
    "commit": r"\.commit\s*\(",
    "connect": r"(?<![\w])(?:" + _DB_CONNECT_OWNERS + r")\.connect\s*\(",
    "executemany": r"\.executemany\s*\(",
    "cursor": r"\.cursor\s*\(",
}
IO_PATTERNS = {
    "open": r"(?<![\w])(?:open|builtins\.open)\s*\(",
    "json_dump": r"(?<![\w])json\.(dump|dumps)\s*\(",
    "json_load": r"(?<![\w])json\.(load|loads)\s*\(",
    "yaml_dump": r"(?<![\w])yaml\.(dump|safe_dump)\s*\(",
    "yaml_load": r"(?<![\w])yaml\.(load|safe_load|full_load)\s*\(",
    "pickle": r"(?<![\w])pickle\.(dump|load|dumps|loads)\s*\(",
    "file_write": r"\.(write|writelines)\s*\(",
    "file_read": r"\.(read|readlines|readline)\s*\(",
    "path_write": r"\.(write_text|write_bytes)\s*\(",
    "path_read": r"\.(read_text|read_bytes)\s*\(",
}
def _call_owner_path(node: ast.expr) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        owner = _call_owner_path(node.value)
        return f"{owner}.{node.attr}" if owner else node.attr
    return ""
def _resolve_import_alias(owner: str, import_aliases: dict[str, str]) -> str:
    first, separator, remainder = owner.partition(".")
    if first not in import_aliases:
        return owner
    qualified = import_aliases[first]
    if not qualified:
        return ""
    return qualified + (separator + remainder if separator else "")
def _call_pattern_targets(
        func: ast.expr, import_aliases: dict[str, str] | None = None,
) -> list[str]:
    aliases = import_aliases or {}
    if isinstance(func, ast.Name):
        if func.id not in aliases:
            return [f"{func.id}("]
        qualified = aliases[func.id]
        return [f"{qualified}("] if qualified else []
    if not isinstance(func, ast.Attribute):
        return []
    targets = [f".{func.attr}("]
    owner = _call_owner_path(func.value)
    if owner:
        binding = owner.partition(".")[0]
        if binding in aliases:
            qualified = _resolve_import_alias(owner, aliases)
            if qualified:
                targets.append(f"{qualified}.{func.attr}(")
        else:
            targets.append(f"{owner}.{func.attr}(")
    return targets
@dataclass(frozen=True)
class _FileMetrics:
    filename: str
    lines: int
    size_bytes: int
    public_symbols: int
    sql_ops: int
    io_ops: int
    parse_error: str = ""
def _parse_source(
        source: str,
        filename: str = DEFAULT_VIRTUAL_FILENAME,
) -> tuple[ast.Module | None, str]:
    try:
        return ast.parse(source, filename=filename), ""
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc,
                      context=f'_parse_source:{type(exc).__name__}')
        return None, str(exc)
class _AliasScope:
    def __init__(self, parent: _AliasScope | None = None, *,
                 is_class: bool = False,
                 is_comprehension: bool = False) -> None:
        self.parent = parent
        self.is_class = is_class
        self.is_comprehension = is_comprehension
        self.aliases: dict[str, str] = {}
        self.rebound: set[str] = set()
        self.events: dict[str, list[tuple[int, str | None]]] = {}
        self.deleted_events: set[tuple[str, int]] = set()
        self.global_names: set[str] = set()
        self.nonlocal_names: set[str] = set()
class _CallAliasCollector(ast.NodeVisitor):
    def __init__(self) -> None:
        self.root = _AliasScope()
        self.scope = self.root
        self._event_sequence = 0
        self._annotations_deferred = False
        self._pending_nonlocal: list[
            tuple[str, str | None, _AliasScope, int, bool]
        ] = []
        self.calls: list[tuple[ast.Call, _AliasScope, int]] = []
    @staticmethod
    def _arguments(args: ast.arguments) -> list[ast.arg]:
        return [
            *args.posonlyargs, *args.args, *args.kwonlyargs,
            *([args.vararg] if args.vararg else []),
            *([args.kwarg] if args.kwarg else []),
        ]
    def _visit_def_site(self, node: ast.FunctionDef | ast.AsyncFunctionDef
                        | ast.Lambda | ast.ClassDef) -> None:
        for decorator in getattr(node, "decorator_list", ()):
            self.visit(decorator)
        args = getattr(node, "args", None)
        if args is not None:
            for default in args.defaults:
                self.visit(default)
            for default in args.kw_defaults:
                if default is not None:
                    self.visit(default)
            if not self._annotations_deferred:
                for arg in self._arguments(args):
                    if arg.annotation is not None:
                        self.visit(arg.annotation)
        returns = getattr(node, "returns", None)
        if returns is not None and not self._annotations_deferred:
            self.visit(returns)
        for base in getattr(node, "bases", ()):
            self.visit(base)
        for keyword_node in getattr(node, "keywords", ()):
            self.visit(keyword_node.value)
        for type_param in getattr(node, "type_params", ()) or ():
            for attr in ("bound", "default"):
                expression = getattr(type_param, attr, None)
                if expression is not None:
                    self.visit(expression)
    def _binding_scope(self, name: str) -> _AliasScope:
        if name in self.scope.global_names:
            return self.root
        return self.scope
    @staticmethod
    def _record_binding(target: _AliasScope, name: str,
                        alias: str | None, sequence: int,
                        deleted: bool = False) -> None:
        if alias is None:
            target.rebound.add(name)
        else:
            target.aliases[name] = alias
        target.events.setdefault(name, []).append((sequence, alias))
        if deleted:
            target.deleted_events.add((name, sequence))
    def _bind(self, name: str | None, alias: str | None = None, *,
              deleted: bool = False) -> None:
        if not name:
            return
        self._event_sequence += 1
        if self.scope is not self.root and name in self.scope.nonlocal_names:
            self._pending_nonlocal.append(
                (name, alias, self.scope, self._event_sequence, deleted))
            return
        self._record_binding(
            self._binding_scope(name), name, alias, self._event_sequence,
            deleted=deleted)
    def _finalize_nonlocal_bindings(self) -> None:
        for name, alias, origin, sequence, deleted in self._pending_nonlocal:
            fallback = origin.parent
            while fallback is not None and fallback.is_class:
                fallback = fallback.parent
            target = fallback
            while target is not None and target is not self.root:
                if name in target.aliases or name in target.rebound:
                    break
                target = target.parent
                while target is not None and target.is_class:
                    target = target.parent
            self._record_binding(target or fallback or self.root,
                                 name, alias, sequence, deleted=deleted)
    def _enter_scope(self, *, is_class: bool = False,
                     is_comprehension: bool = False) -> _AliasScope:
        previous = self.scope
        self.scope = _AliasScope(
            previous, is_class=is_class, is_comprehension=is_comprehension)
        return previous
    def visit_Import(self, node: ast.Import) -> None:
        for imported in node.names:
            if imported.asname:
                self._bind(imported.asname, imported.name)
            else:
                first = imported.name.partition(".")[0]
                self._bind(first, first)
    def visit_ImportFrom(self, node: ast.ImportFrom) -> None:
        if (not node.level and node.module == "__future__"
                and any(imported.name == "annotations"
                        for imported in node.names)):
            self._annotations_deferred = True
        for imported in node.names:
            if imported.name == "*":
                continue
            local_name = imported.asname or imported.name
            qualified = (f"{node.module}.{imported.name}"
                         if not node.level and node.module else "")
            self._bind(local_name, qualified)
    def visit_Name(self, node: ast.Name) -> None:
        if isinstance(node.ctx, ast.Store):
            self._bind(node.id)
        elif isinstance(node.ctx, ast.Del):
            self._bind(node.id, deleted=True)
    def _assigned_alias(self, value: ast.expr) -> str | None:
        owner = _call_owner_path(value)
        if not owner:
            return None
        binding = owner.partition(".")[0]
        qualified = self.resolve(self.scope, binding, self._event_sequence)
        if qualified is None:
            qualified = binding
        if not qualified:
            return ""
        return _resolve_import_alias(owner, {binding: qualified})
    def _visit_assignment_value(self, value: ast.expr) -> Any:
        if (isinstance(value, (ast.Tuple, ast.List))
                and all(not isinstance(item, ast.Starred)
                        for item in value.elts)):
            return [self._visit_assignment_value(item) for item in value.elts]
        self.visit(value)
        return self._assigned_alias(value)
    def _bind_assigned_target(self, target: ast.expr, alias: Any) -> None:
        if isinstance(target, ast.Name):
            self._bind(
                target.id,
                alias if alias is None or isinstance(alias, str) else None)
            return
        if (isinstance(target, (ast.Tuple, ast.List))
                and isinstance(alias, list)
                and len(target.elts) == len(alias)
                and all(not isinstance(item, ast.Starred)
                        for item in target.elts)):
            for target_item, item_alias in zip(target.elts, alias):
                self._bind_assigned_target(target_item, item_alias)
            return
        self.visit(target)
    def visit_Assign(self, node: ast.Assign) -> None:
        alias = self._visit_assignment_value(node.value)
        for target in node.targets:
            self._bind_assigned_target(target, alias)
    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if node.value is not None:
            self.visit(node.value)
            alias = self._assigned_alias(node.value)
            self._bind_assigned_target(node.target, alias)
        if (not self._annotations_deferred
                and (self.scope is self.root or self.scope.is_class)):
            self.visit(node.annotation)
        if node.value is None and (isinstance(node.target, ast.Name)
              and self.scope is not self.root and not self.scope.is_class
              and node.target.id not in self.scope.aliases
              and node.target.id not in self.scope.rebound):
            self._bind(node.target.id)
    def visit_AugAssign(self, node: ast.AugAssign) -> None:
        target = node.target
        if isinstance(target, ast.Attribute):
            self.visit(target.value)
        elif isinstance(target, ast.Subscript):
            self.visit(target.value)
            self.visit(target.slice)
        self.visit(node.value)
        if isinstance(target, ast.Name):
            self._bind(target.id)
    def visit_NamedExpr(self, node: ast.NamedExpr) -> None:
        self.visit(node.value)
        alias = self._assigned_alias(node.value)
        target_scope = self.scope
        while target_scope.is_comprehension and target_scope.parent is not None:
            target_scope = target_scope.parent
        previous = self.scope
        self.scope = target_scope
        try:
            self._bind_assigned_target(node.target, alias)
        finally:
            self.scope = previous
    def _visit_for(self, node: ast.For | ast.AsyncFor) -> None:
        self.visit(node.iter)
        self.visit(node.target)
        for statement in (*node.body, *node.orelse):
            self.visit(statement)
    visit_For = _visit_for
    visit_AsyncFor = _visit_for
    def visit_Global(self, node: ast.Global) -> None:
        self.scope.global_names.update(node.names)
    def visit_Nonlocal(self, node: ast.Nonlocal) -> None:
        self.scope.nonlocal_names.update(node.names)
    def visit_ExceptHandler(self, node: ast.ExceptHandler) -> None:
        if node.type is not None:
            self.visit(node.type)
        self._bind(node.name)
        for statement in node.body:
            self.visit(statement)
        self._bind(node.name, deleted=True)
    def visit_MatchAs(self, node: ast.MatchAs) -> None:
        self._bind(node.name)
        self.generic_visit(node)
    def visit_MatchStar(self, node: ast.MatchStar) -> None:
        self._bind(node.name)
    def visit_MatchMapping(self, node: ast.MatchMapping) -> None:
        self._bind(node.rest)
        self.generic_visit(node)
    def visit_Call(self, node: ast.Call) -> None:
        self.calls.append((node, self.scope, self._event_sequence))
        self.generic_visit(node)
    def _visit_function(self, node: ast.FunctionDef | ast.AsyncFunctionDef
                        | ast.Lambda) -> None:
        self._visit_def_site(node)
        if not isinstance(node, ast.Lambda):
            self._bind(node.name)
        previous = self._enter_scope()
        try:
            for arg in self._arguments(node.args):
                self._bind(arg.arg)
            if isinstance(node, ast.Lambda):
                self.visit(node.body)
            else:
                for statement in node.body:
                    self.visit(statement)
        finally:
            self.scope = previous
    visit_FunctionDef = _visit_function
    visit_AsyncFunctionDef = _visit_function
    visit_Lambda = _visit_function
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self._visit_def_site(node)
        previous = self._enter_scope(is_class=True)
        try:
            for statement in node.body:
                self.visit(statement)
        finally:
            self.scope = previous
        self._bind(node.name)
    def _visit_comprehension(self, node: ast.ListComp | ast.SetComp
                             | ast.GeneratorExp | ast.DictComp) -> None:
        generators = node.generators
        if not generators:
            return
        self.visit(generators[0].iter)
        previous = self._enter_scope(is_comprehension=True)
        try:
            for index, generator in enumerate(generators):
                self.visit(generator.target)
                if index:
                    self.visit(generator.iter)
                for condition in generator.ifs:
                    self.visit(condition)
            if isinstance(node, ast.DictComp):
                self.visit(node.key)
                self.visit(node.value)
            else:
                self.visit(node.elt)
        finally:
            self.scope = previous
    visit_ListComp = _visit_comprehension
    visit_SetComp = _visit_comprehension
    visit_GeneratorExp = _visit_comprehension
    visit_DictComp = _visit_comprehension
    @staticmethod
    def _event_at(scope: _AliasScope, name: str,
                  sequence: int | None) -> tuple[int, str | None] | None:
        events = scope.events.get(name, ())
        if sequence is not None:
            events = [event for event in events if event[0] <= sequence]
        if not events:
            return None
        return max(events, key=lambda event: event[0])
    def resolve(self, scope: _AliasScope, name: str,
                sequence: int) -> str | None:
        at_call_scope = True
        suppress_unbound = False
        while scope is not None:
            if scope is not self.root and name in scope.global_names:
                preserve_sequence = at_call_scope and scope.is_class
                scope = self.root
                at_call_scope = preserve_sequence
            elif scope is not self.root and name in scope.nonlocal_names:
                target = scope.parent
                while target is not None and target.is_class:
                    target = target.parent
                if target is not None:
                    scope = target
                    at_call_scope = False
                    continue
            if name in scope.aliases or name in scope.rebound:
                event = self._event_at(
                    scope, name, sequence if at_call_scope else None)
                deleted = (event is not None
                           and (name, event[0]) in scope.deleted_events)
                if event is not None and not deleted:
                    return event[1] or ""
                if scope is not self.root and not scope.is_class:
                    return ""
                if name not in _BUILTIN_NAMES:
                    suppress_unbound = True
            preserve_sequence = at_call_scope and (
                scope.is_class or scope.is_comprehension)
            parent = scope.parent
            if not scope.is_class:
                while parent is not None and parent.is_class:
                    parent = parent.parent
            scope = parent
            at_call_scope = preserve_sequence
        return "" if suppress_unbound else None
def _call_targets(tree: ast.AST) -> list[list[str]]:
    collector = _CallAliasCollector()
    collector.visit(tree)
    collector._finalize_nonlocal_bindings()
    targets = []
    for node, scope, sequence in collector.calls:
        func = node.func
        if isinstance(func, ast.Name):
            binding = func.id
        elif isinstance(func, ast.Attribute):
            binding = _call_owner_path(func.value).partition(".")[0]
        else:
            binding = ""
        qualified = (collector.resolve(scope, binding, sequence)
                     if binding else None)
        aliases = ({binding: qualified}
                   if binding and qualified is not None else {})
        targets.append(_call_pattern_targets(func, aliases))
    return targets
def _count_calls(targets: list[list[str]],
                 patterns: dict[str, str]) -> int:
    return sum(
        1
        for call_targets in targets
        for pattern in patterns.values()
        if any(re.search(pattern, target) for target in call_targets)
    )
def _measure_source(source: str, filename: str,
                    size_bytes: int) -> _FileMetrics:
    tree, parse_error = _parse_source(source, filename)
    lines = count_lines(source)
    if tree is None:
        return _FileMetrics(filename, lines, size_bytes, 0, 0, 0, parse_error)
    targets = _call_targets(tree)
    return _FileMetrics(
        filename=filename,
        lines=lines,
        size_bytes=size_bytes,
        public_symbols=sum(
            1 for node in tree.body
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.ClassDef))
            and not node.name.startswith("_")),
        sql_ops=_count_calls(targets, SQL_PATTERNS),
        io_ops=_count_calls(targets, IO_PATTERNS),
    )
def _measure_file(path: str | Path,
                  filename: str | None = None) -> _FileMetrics:
    raw = Path(path).read_bytes()
    source = decode_source_bytes(raw)
    return _measure_source(source, filename or Path(path).name, len(raw))
def _is_profile_dir(name: str, skip: frozenset[str] | set[str],
                    root_dir: str) -> bool:
    return (not name.startswith(".")
            and name.lower() not in skip
            and not is_archive_or_cache_path(name, root_dir=root_dir))
def _is_profile_candidate(name: str, ext: str) -> bool:
    return not name.startswith(".") and name.lower().endswith(ext.lower())
def _profile_entry(metrics: _FileMetrics, rel_path: str) -> dict:
    entry = {
        "file": rel_path,
        "lines": metrics.lines,
        "sql_ops": metrics.sql_ops,
        "io_ops": metrics.io_ops,
        "size_bytes": metrics.size_bytes,
    }
    if metrics.parse_error:
        entry["parse_error"] = metrics.parse_error
    return entry
def _zero_profile_entry(filepath: str) -> dict:
    return {"file": filepath, "lines": 0, "sql_ops": 0,
            "io_ops": 0, "size_bytes": 0}
def profile_file(filepath: str, content: str | bytes | None = None) -> dict:
    filepath = _coerce_path_text(filepath)
    if not filepath:
        _log.warning("profile_file: 文件路径为空或类型非法（%r），返回零值画像",
                     filepath)
        return _zero_profile_entry("")
    raw_content: bytes | None = None
    if isinstance(content, (bytes, bytearray)):
        raw_content = bytes(content)
        content = decode_source_bytes(raw_content)
    elif content is not None and not isinstance(content, str):
        raise TypeError(
            "profile_file: content 须为 str/bytes/None，实际为 "
            f"{type(content).__name__}")
    if content is None:
        try:
            metrics = _measure_file(filepath)
        except OSError as e:
            _log.warning("profile_file(%s) 读取失败: %s", filepath, e)
            return _zero_profile_entry(filepath)
        return _profile_entry(metrics, filepath)
    size_bytes = (len(raw_content) if raw_content is not None else
                  len(content.encode("utf-8", errors="replace")))
    return _profile_entry(_measure_source(content, filepath, size_bytes), filepath)
def _walk_files(directory: str, keep_dir: Callable[[str], bool],
                keep_file: Callable[[str], bool]) -> list[Path]:
    found: list[Path] = []
    def _on_walk_error(err: OSError) -> None:
        _log.warning("目录遍历中断（保留已发现结果）: %s: %s", directory, err)
    for root, dirs, files in os.walk(directory, onerror=_on_walk_error):
        dirs[:] = [d for d in dirs if keep_dir(d)]
        root_path = Path(root)
        found.extend(root_path / name for name in files if keep_file(name))
    return sorted(found, key=lambda path: safe_relpath(str(path), directory))
def profile_directory(directory: str, ext: str = ".py") -> list[dict]:
    root = _require_scan_root(directory, "profile_directory")
    root_text = str(root)
    ext = norm_text(ext) or ".py"
    skip = scan_prune_dirs(root_text)
    results = []
    for path in _walk_files(
            root_text, lambda name: _is_profile_dir(name, skip, root_text),
            lambda name: _is_profile_candidate(name, ext)):
        rel_path = safe_relpath(str(path), root_text)
        if is_archive_or_cache_path(rel_path, root_dir=root_text):
            continue
        try:
            metrics = _measure_file(path, rel_path)
        except OSError as e:
            _log.warning("profile_directory 读取跳过 %s: %s", rel_path, e)
            continue
        results.append(_profile_entry(metrics, rel_path))
    return results
def summarize_sql_by_dir(profile_results: list[dict]) -> dict[str, int]:
    dirs: dict[str, int] = {}
    for info in norm_entity_list(profile_results):
        if not isinstance(info, dict):
            continue
        rel_path = str(info.get("file") or "").replace("\\", "/")
        d = os.path.dirname(rel_path) or "(root)"
        dirs[d] = dirs.get(d, 0) + int_metric(info.get("sql_ops"))
    return dict(sorted(dirs.items(), key=lambda x: (-x[1], x[0])))
def _is_manifest_candidate(name: str) -> bool:
    return (_is_profile_candidate(name, ".py")
            and not is_test_source_basename(name))
def _manifest_record(metrics: _FileMetrics) -> dict[str, Any]:
    entry: dict[str, Any] = {
        "filename": metrics.filename,
        "size_bytes": metrics.size_bytes,
        "size_kb": round(metrics.size_bytes / 1024, 1),
        "lines": metrics.lines,
        "public_symbols": metrics.public_symbols,
        "sql_ops": metrics.sql_ops,
        "io_ops": metrics.io_ops,
    }
    if metrics.parse_error:
        _log.warning("解析跳过 %s: %s", metrics.filename, metrics.parse_error)
        entry["parse_error"] = metrics.parse_error
    return entry
def _data_profile_summary(profiles: list[dict]) -> dict[str, Any]:
    rows = [
        {"file": normalize_rel_path(norm_text(p.get("file"))),
         "sql_ops": int_metric(p.get("sql_ops")),
         "io_ops": int_metric(p.get("io_ops"))}
        for p in norm_entity_list(profiles) if isinstance(p, dict)
    ]
    ordered = sorted(rows, key=lambda p: (-p["sql_ops"], p["file"]))
    return {
        "total_sql_ops": sum(p["sql_ops"] for p in ordered),
        "total_io_ops": sum(p["io_ops"] for p in ordered),
        "sql_by_dir": summarize_sql_by_dir(ordered),
        "top_sql_files": [
            {"file": p["file"], "sql_ops": p["sql_ops"], "io_ops": p["io_ops"]}
            for p in ordered[:10] if p["sql_ops"] > 0
        ],
    }
def _manifest_entries(metrics: Iterable[_FileMetrics]) -> list[dict[str, Any]]:
    return [_manifest_record(item) for item in metrics]
def _scan_skill_files(root_text: str) -> list[_FileMetrics]:
    root = Path(root_text)
    metrics: list[_FileMetrics] = []
    for path in _collect_python_files(root, scan_exclude_dirs(root_text)):
        if not _is_manifest_candidate(path.name):
            continue
        rel_path = safe_relpath(str(path), root_text)
        try:
            metrics.append(_measure_file(path, rel_path))
        except OSError as e:
            _log.warning("读取跳过 %s: %s", rel_path, e)
    return metrics
def scan_file_manifest(skill_dir: str) -> list[dict[str, Any]]:
    root_text = str(_require_scan_root(skill_dir, "scan_file_manifest"))
    return _manifest_entries(_scan_skill_files(root_text))
def scan_full_analysis_files(skill_dir: str) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    root_text = str(_require_scan_root(skill_dir, "scan_full_analysis_files"))
    metrics = _scan_skill_files(root_text)
    manifest = _manifest_entries(metrics)
    profile = _data_profile_summary(
        [_profile_entry(item, item.filename) for item in metrics])
    return manifest, profile
def normalize_scan_modules(scan: dict) -> list:
    if not isinstance(scan, dict):
        return []
    modules = scan.get("modules")
    if not isinstance(modules, list):
        return []
    return [m for m in modules if isinstance(m, dict)]
_STDLIB_NAMES = frozenset(sys.stdlib_module_names)
_UNNAMED_MODULE = "未命名模块"
_DOC_SKIP_PREFIXES = ("Args", "Returns", "Raises", "Note", "Example")
_DOC_SKIP_PREFIXES_LOWER = tuple(p.lower() for p in _DOC_SKIP_PREFIXES)
def one_line(text: Any, limit: int = 0) -> str:
    if not isinstance(text, str):
        text = "" if text is None else str(text)
    flat = " ".join(text.split())
    limit = int_metric(limit)
    if limit > 0 and len(flat) > limit:
        if limit <= 3:
            return flat[:limit]
        return flat[:limit - 3] + "..."
    return flat
def skill_label(skill_name: Any) -> str:
    return norm_text(skill_name).strip() or "本技能"
def _is_py_name(value: Any) -> bool:
    return (isinstance(value, str) and value.isidentifier()
            and not keyword.iskeyword(value))
def _norm_scan(scan_result: Any) -> dict:
    return scan_result if isinstance(scan_result, dict) else {}
def norm_entity_list(value: Any) -> list:
    if isinstance(value, (list, tuple)):
        return list(value)
    if isinstance(value, (str, bytes, bytearray, dict)):
        return []
    if isinstance(value, Iterable):
        return list(value)
    return []
def _effective_doc_first_line(full_doc: str, doc: str) -> str:
    candidates = (first_line(full_doc), first_line(doc))
    for candidate in candidates:
        if candidate and not candidate.lower().startswith(
                _DOC_SKIP_PREFIXES_LOWER):
            return candidate
    return ""
def _summary_counts(scan_result: Any) -> tuple[int, int, int, int, int, int]:
    scan = _norm_scan(scan_result)
    modules = normalize_scan_modules(scan)
    if modules:
        def module_metric(key: str, total_key: str, count: Callable) -> int:
            if not all(key in module for module in modules):
                return int_metric(scan.get(total_key))
            return sum(count(module.get(key)) for module in modules)
        def entity_count(value: Any) -> int:
            return len(entity_names(norm_entity_list(value)))
        def export_count(value: Any) -> int:
            return len([name for name in norm_entity_list(value)
                        if isinstance(name, str) and name.strip()])
        return (
            len(modules),
            module_metric("lines", "total_lines", int_metric),
            module_metric("functions", FIELD_TOTAL_FUNCTIONS, entity_count),
            module_metric("classes", "total_classes", entity_count),
            module_metric("exports", "total_exports", export_count),
            module_metric("constants", "total_constants", entity_count),
        )
    return (
        int_metric(scan.get("total_modules")),
        int_metric(scan.get("total_lines")),
        int_metric(scan.get(FIELD_TOTAL_FUNCTIONS)),
        int_metric(scan.get("total_classes")),
        int_metric(scan.get("total_exports")),
        int_metric(scan.get("total_constants")),
    )
def _capability_summary_line(scan_result: dict) -> str:
    mods, lines, funcs, classes, exports, total_consts = _summary_counts(
        scan_result)
    consts_str = f" | {total_consts} 个模块常量" if total_consts > 0 else ""
    return (f"共 **{mods}** 个模块 | {lines} 行代码 "
            f"| {funcs} 个公开函数 "
            f"| {classes} 个公开类 "
            f"| {exports} 个公开导出{consts_str}")
def _capability_api_summary(funcs: list, classes: list) -> str:
    func_names = entity_names(funcs)
    class_names = entity_names(classes)
    api_parts = [f"`{md_escape_cell(n)}()`"
                 for n in func_names[:_RENDER_LIMIT_API_FUNCS]]
    api_parts.extend(f"`{md_escape_cell(n)}`"
                     for n in class_names[:_RENDER_LIMIT_API_CLASSES])
    api_str = ", ".join(api_parts) if api_parts else "-"
    remaining = (max(0, len(func_names) - _RENDER_LIMIT_API_FUNCS)
                 + max(0, len(class_names) - _RENDER_LIMIT_API_CLASSES))
    return f"{api_str} 等+{remaining}" if remaining > 0 else api_str
def _profile_table_cells(mod: dict, limit: int) -> tuple[str, int, str, str]:
    path = md_escape_cell(norm_text(mod.get("path")))
    lines = int_metric(mod.get("lines"))
    cat = md_escape_cell(norm_text(mod.get("category"), "-").strip() or "-")
    purpose = (norm_text(mod.get("purpose")).strip()
               or norm_text(mod.get("doc_summary")).strip())
    if not purpose:
        purpose = "; ".join(clean_str_list(mod.get("key_capabilities"))[:2])
    return path, lines, cat, one_line(purpose, limit) if purpose else "-"
def _capability_table_row(mod: dict) -> str:
    path, lines, cat, capability = _profile_table_cells(mod, 100)
    api_str = _capability_api_summary(
        norm_entity_list(mod.get("functions")),
        norm_entity_list(mod.get("classes")))
    return (f"| `{path}` | {lines} | {cat} "
            f"| {md_escape_cell(capability)} | {api_str} |")
def render_module_capability_table(scan_result: dict) -> str:
    lines = []
    scan_result = _norm_scan(scan_result)
    modules = normalize_scan_modules(scan_result)
    lines.append(_capability_summary_line(scan_result))
    lines.append("")
    lines.append("| 模块 | 行数 | 分类 | 核心能力 | 主要公开 API |")
    lines.append("|------|------|------|---------|-------------|")
    for mod in modules:
        lines.append(_capability_table_row(mod))
    return "\n".join(lines)
def render_scan_summary(scan_result: Any) -> str:
    total_mods, total_lines, total_funcs, total_cls, total_exp, _consts = (
        _summary_counts(scan_result))
    return (f"{total_mods} 个模块 | {total_lines} 行代码"
            f" | {total_funcs} 个公开函数 | {total_cls} 个公开类"
            f" | {total_exp} 个公开导出")
_RENDER_LIMIT_EXPORTS = 30
_RENDER_LIMIT_CONSTANTS = 10
_RENDER_LIMIT_METHODS = 15
_RENDER_LIMIT_API_FUNCS = 8
_RENDER_LIMIT_API_CLASSES = 5
_RENDER_LIMIT_DEPS = 10
def _rebuild_param_strs(params: list) -> list[str]:
    has_vararg = any(p.get("kind") == "vararg" for p in params)
    last_posonly = max((idx for idx, p in enumerate(params)
                        if p.get("posonly") is True), default=-1)
    param_strs = []
    star_inserted = False
    for idx, p in enumerate(params):
        kind = p.get("kind")
        if kind == "keyword" and not star_inserted and not has_vararg:
            param_strs.append("*")
            star_inserted = True
        prefix = {"vararg": "*", "kwarg": "**"}.get(kind, "")
        pstr = prefix + str(p["name"])
        ptype = p.get("type")
        if ptype:
            pstr += f": {ptype}"
        if p.get("default") is not None:
            pstr += f" = {p['default']}"
        param_strs.append(pstr)
        if idx == last_posonly:
            param_strs.append("/")
    return param_strs
def _decorator_prefix(func: dict) -> str:
    decos = [d for d in norm_entity_list(func.get("decorators"))
             if isinstance(d, str) and d]
    return f" @({' @'.join(decos)})" if decos else ""
def _render_function_line(func: dict) -> str | None:
    fname = entity_name(func)
    if not fname:
        return None
    params = [p for p in norm_entity_list(func.get("params"))
              if isinstance(p, dict) and _is_py_name(p.get("name"))]
    async_prefix = "async " if func.get("is_async") is True else ""
    sig = f"{async_prefix}{fname}({', '.join(_rebuild_param_strs(params))})"
    returns = norm_text(func.get("returns")).strip()
    ret = f" -> {returns}" if returns else ""
    deco_str = _decorator_prefix(func)
    desc = _effective_doc_first_line(
        norm_text(func.get("full_doc")), norm_text(func.get("doc")))
    line = f"-{deco_str} `{sig}{ret}`"
    return f"{line} — {desc}" if desc else line
def _render_functions_section(funcs: list) -> list:
    body: list[str] = []
    for func in funcs:
        line = _render_function_line(func)
        if line:
            body.append(line)
    if not body:
        return []
    return ["**公开函数**:", "", *body, ""]
def _class_method_names(c: dict) -> list:
    methods = [m for m in norm_entity_list(c.get("public_methods"))
               if isinstance(m, dict)]
    method_names = entity_names(methods)
    if not method_names:
        method_names = [m for m in norm_entity_list(c.get("all_methods"))
                        if isinstance(m, str) and m]
    return method_names
def _render_class_block(cls: dict) -> list[str]:
    cname = one_line(entity_name(cls)).strip()
    if not cname:
        return []
    bases = [one_line(b).strip() for b in norm_entity_list(cls.get("bases"))
             if isinstance(b, str) and b.strip()]
    base_str = f"({', '.join(bases)})" if bases else ""
    cls_desc = _effective_doc_first_line(
        norm_text(cls.get("full_doc")), norm_text(cls.get("doc")))
    desc_str = f" — {cls_desc}" if cls_desc else ""
    block = [f"- `{cname}{base_str}`{desc_str}"]
    method_names = [name.strip()
                    for name in map(one_line, _class_method_names(cls))
                    if name.strip()]
    if method_names:
        visible, tail = _clip_with_remainder(method_names, _RENDER_LIMIT_METHODS)
        methods_str = ", ".join(f"`{m}()`" for m in visible)
        block.append(f"  方法: {methods_str}{tail}")
    return block
def _render_classes_section(classes: list) -> list:
    body: list[str] = []
    for cls in classes:
        body.extend(_render_class_block(cls))
    if not body:
        return []
    return ["**公开类**:", "", *body, ""]
def _required_params_example(entry_func: dict) -> str:
    required = []
    for p in norm_entity_list(entry_func.get("params")):
        if not isinstance(p, dict):
            continue
        pname = p.get("name")
        if not _is_py_name(pname):
            continue
        if p.get("default") is not None:
            continue
        if p.get("kind") in ("vararg", "kwarg"):
            continue
        if p.get("kind") == "keyword":
            required.append(f"{pname}=...")
        else:
            required.append("...")
    return ", ".join(required)
def _format_call_example(mod_import: str, import_name: str,
                         body_line: str = "",
                         import_suffix: str = "",
                         prelude: str = "") -> list[str]:
    lines_out = [
        "**调用示例**:",
        "```python",
    ]
    if prelude:
        lines_out.append(prelude)
    lines_out.append(f"from {mod_import} import {import_name}{import_suffix}")
    if body_line:
        lines_out.append(body_line)
    lines_out.extend(["```", ""])
    return lines_out
def _norm_import_root(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    name = value.strip()
    return name if _is_py_name(name) else ""
def _dotted_import_name(mod: dict | str) -> str | None:
    raw_path = mod.get("path") if isinstance(mod, dict) else mod
    rel_path = normalize_rel_path(norm_text(raw_path))
    if not rel_path:
        return None
    segments = rel_path.split("/")
    segments[-1] = py_stem(segments[-1])
    if not all(_is_py_name(seg) for seg in segments):
        return None
    if segments[-1] == "__init__":
        segments.pop()
    return ".".join(segments)
def _render_function_example(mod_import: str, entry_func: dict) -> list[str]:
    name = entity_name(entry_func)
    args = _required_params_example(entry_func)
    if entry_func.get("is_async") is True:
        return _format_call_example(
            mod_import, name,
            f"result = asyncio.run({name}({args}))",
            prelude="import asyncio")
    return _format_call_example(
        mod_import, name, f"result = {name}({args})")
def _render_class_example(mod_import: str, entry_class: dict) -> list[str]:
    name = entity_name(entry_class)
    init_params = [p for p in norm_entity_list(entry_class.get("init_params"))
                   if isinstance(p, dict)]
    args = _required_params_example({"params": init_params})
    return _format_call_example(
        mod_import, name,
        f"instance = {name}({args})  # 查阅类方法列表获取可用操作")
def _render_internal_module_note(mod_import: str) -> list[str]:
    return [
        ("**使用说明**: 此模块为内部辅助模块，无公开函数/类/导出。"
         f"通过 `import {mod_import}` 整体引用或被其他模块内部调用。"),
        "",
    ]
_UNRESOLVED_IMPORT_NOTE = (
    "**使用说明**: 此模块画像缺少有效路径或文件名不可导入，"
    "无法生成可靠的导入示例。")
def _render_usage_example(mod: dict, funcs: list, classes: list, exports: list,
                           import_root: str) -> list:
    if "import_name" in mod:
        scanned_name = mod.get("import_name")
        mod_import = scanned_name if isinstance(scanned_name, str) else ""
        if mod_import and not all(
                _is_py_name(segment) for segment in mod_import.split(".")):
            return [_UNRESOLVED_IMPORT_NOTE, ""]
    else:
        mod_dotted = _dotted_import_name(mod)
        if mod_dotted is None:
            return [_UNRESOLVED_IMPORT_NOTE, ""]
        import_root_name = _norm_import_root(import_root)
        if import_root_name and (
                mod_dotted == import_root_name
                or mod_dotted.startswith(import_root_name + ".")):
            mod_import = mod_dotted
        else:
            mod_import = ".".join(
                part for part in (import_root_name, mod_dotted) if part)
    if not mod_import and "import_name" in mod:
        return [_UNRESOLVED_IMPORT_NOTE, ""]
    if not mod_import:
        return [("**使用说明**: 此模块为包根初始化文件且画像缺少可导入的包名前缀，"
                 "无法生成可靠的导入示例。"), ""]
    named_funcs = [item for item in norm_entity_list(funcs)
                   if _is_py_name(entity_name(item))]
    named_classes = [item for item in norm_entity_list(classes)
                     if _is_py_name(entity_name(item))]
    clean_exports = [name for name in norm_entity_list(exports)
                     if _is_py_name(name)]
    if named_funcs:
        return _render_function_example(mod_import, named_funcs[0])
    if named_classes:
        return _render_class_example(mod_import, named_classes[0])
    if clean_exports:
        return _format_call_example(mod_import, clean_exports[0],
                                    import_suffix="  # 常量/数据引用")
    return _render_internal_module_note(mod_import)
def _render_module_header(mod: dict, path: str, cat: str, key_caps: list) -> list:
    path = one_line(norm_text(path)).strip()
    cat = one_line(norm_text(cat)).strip()
    lines_out = []
    lines_out.append(f"### `{path or _UNNAMED_MODULE}`")
    lines_out.append("")
    purpose = norm_text(mod.get("purpose"))
    meta_parts = [f"{int_metric(mod.get('lines'))} 行"]
    if cat:
        meta_parts.append(f"分类: {cat}")
    lines_out.append(f"> {' | '.join(meta_parts)}")
    lines_out.append("")
    trigger_info = _build_agent_trigger_info(path, purpose, key_caps, cat)
    lines_out.append(trigger_info)
    lines_out.append("")
    return lines_out
def _clip_with_remainder(items: list, limit: int) -> tuple:
    if limit <= 0 or len(items) <= limit:
        return items, ""
    return items[:limit], f" … 等 {len(items) - limit} 项"
def _render_module_metadata_sections(exports: list, constants: list) -> list:
    lines_out = []
    if exports:
        visible, tail = _clip_with_remainder(exports, _RENDER_LIMIT_EXPORTS)
        lines_out.append(f"**公开导出** ({len(exports)} 项): "
                         f"{', '.join(f'`{e}`' for e in visible)}{tail}")
        lines_out.append("")
    if constants:
        visible, tail = _clip_with_remainder(constants, _RENDER_LIMIT_CONSTANTS)
        lines_out.append(f"**模块级常量** ({len(constants)} 项):")
        for c in visible:
            const_name = one_line(entity_name(c)).strip()
            if not const_name:
                continue
            val = c.get("value")
            if val is None or (isinstance(val, str) and not val):
                lines_out.append(f"  - `{const_name}`")
            else:
                lines_out.append(f"  - `{const_name}` = {one_line(val)}")
        if tail:
            lines_out.append(f"  -{tail}")
        lines_out.append("")
    return lines_out
def _filter_external_deps(all_imports: list, internal_deps: list,
                          import_root: str, module_stems: set) -> list:
    internal_first = set(module_stems)
    if not import_root:
        internal_first.update(
            str(dep).split(".", maxsplit=1)[0]
            for dep in internal_deps if dep)
    root_prefix = f"{import_root}." if import_root else ""
    external = []
    for imp in all_imports:
        first = imp.split(".", maxsplit=1)[0]
        if import_root and (imp == import_root or imp.startswith(root_prefix)):
            continue
        if first in internal_first or first in _STDLIB_NAMES:
            continue
        external.append(imp)
    return external
def _dependency_lines(prefix: str, deps: list[str]) -> list[str]:
    deps = [one_line(dep).strip() for dep in deps if dep]
    deps = [dep for dep in deps if dep]
    if not deps:
        return []
    visible, tail = _clip_with_remainder(deps, _RENDER_LIMIT_DEPS)
    return [f"{prefix}{', '.join(f'`{d}`' for d in visible)}{tail}", ""]
def _render_module_deps_sections(mod: dict, import_root: str,
                                 module_stems: set) -> list:
    internal_deps = [d for d in norm_entity_list(mod.get("internal_imports"))
                     if isinstance(d, str) and d]
    all_imports = [imp for imp in norm_entity_list(mod.get("imports"))
                   if isinstance(imp, str) and imp]
    external_deps = _filter_external_deps(all_imports, internal_deps,
                                          import_root, module_stems)
    return (_dependency_lines("**内部依赖** (引用同技能模块): ", internal_deps)
            + _dependency_lines("**外部依赖** (第三方库): ", external_deps))
def _module_entities(mod: dict) -> tuple[list, list, list[str], list[dict]]:
    funcs = norm_entity_list(mod.get("functions"))
    classes = norm_entity_list(mod.get("classes"))
    exports = []
    for export in norm_entity_list(mod.get("exports")):
        if not isinstance(export, str):
            continue
        safe_export = one_line(export).strip()
        if safe_export:
            exports.append(safe_export)
    constants = [c for c in norm_entity_list(mod.get("constants"))
                 if isinstance(c, dict) and entity_name(c)]
    return funcs, classes, exports, constants
_ATX_LINE_RE = re.compile(r"^[ \t]{0,3}#{1,6}(?:\s|$)")
_SETEXT_RULE_RE = re.compile(r"^[ \t]{0,3}(?:-{3,}|={3,})[ \t]*$")
_FENCE_LINE_RE = re.compile(r"^[ \t]{0,3}(?:`{3,}|~{3,})")
def _escape_block_markup(doc: str) -> str:
    block_patterns = (_ATX_LINE_RE, _SETEXT_RULE_RE, _FENCE_LINE_RE)
    lines_out = []
    for line in doc.splitlines():
        if any(pattern.match(line) for pattern in block_patterns):
            indent = len(line) - len(line.lstrip(" \t"))
            line = line[:indent] + "\\" + line[indent:]
        lines_out.append(line)
    return "\n".join(lines_out)
def _render_module_prose(doc: str, key_caps: list[str]) -> list[str]:
    lines_out: list[str] = []
    if doc:
        lines_out.extend([_escape_block_markup(doc), ""])
    caps = [one_line(cap).strip() for cap in key_caps]
    caps = [cap for cap in caps if cap]
    if caps:
        lines_out.extend([f"**核心能力**: {'; '.join(caps)}", ""])
    return lines_out
def _render_single_module(mod: dict, import_root: str,
                          module_stems: set) -> list:
    lines_out = []
    path = norm_text(mod.get("path"))
    cat = norm_text(mod.get("category"))
    doc = norm_text(mod.get("doc"))
    key_caps = clean_str_list(mod.get("key_capabilities"))
    lines_out.extend(_render_module_header(mod, path, cat, key_caps))
    lines_out.extend(_render_module_prose(doc, key_caps))
    funcs, classes, exports, constants = _module_entities(mod)
    if funcs:
        lines_out.extend(_render_functions_section(funcs))
    if classes:
        lines_out.extend(_render_classes_section(classes))
    lines_out.extend(_render_module_metadata_sections(exports, constants))
    lines_out.extend(_render_module_deps_sections(mod, import_root,
                                                  module_stems))
    lines_out.extend(_render_usage_example(mod, funcs, classes, exports,
                                           import_root))
    lines_out.append("---")
    lines_out.append("")
    return lines_out
def _inside_import_root(mod: dict, import_root: str) -> bool:
    if not import_root:
        return False
    import_name = mod.get("import_name")
    if isinstance(import_name, str) and import_name:
        return (import_name == import_root
                or import_name.startswith(import_root + "."))
    parts = normalize_rel_path(norm_text(mod.get("path"))).split("/")
    return import_root in parts[:-1]
def render_full_module_capabilities(scan_result: dict) -> str:
    lines_out = []
    scan_result = _norm_scan(scan_result)
    modules = normalize_scan_modules(scan_result)
    import_root = _norm_import_root(scan_result.get("import_root"))
    if not modules:
        _log.debug("render_full_module_capabilities: 扫描画像无模块数据,渲染空章节")
    module_stems = set()
    for mod in modules:
        if _inside_import_root(mod, import_root):
            continue
        stem = module_stem(mod.get("path"))
        if stem:
            module_stems.add(stem)
        import_name = mod.get("import_name")
        if isinstance(import_name, str) and import_name:
            module_stems.add(import_name.split(".", maxsplit=1)[0])
        parts = normalize_rel_path(norm_text(mod.get("path"))).split("/")
        if len(parts) > 1 and _is_py_name(parts[0]):
            module_stems.add(parts[0])
    for mod in modules:
        lines_out.extend(_render_single_module(mod, import_root, module_stems))
    return "\n".join(lines_out)
_FUNC_VERB_CAP_MAP = [
    ("diag", "代码诊断"), ("detect", "问题检测"),
    ("scan", "代码扫描"), ("fix", "自动修复"),
    ("clean", "代码清理"), ("refactor", "重构"),
    ("build", "构建生成"), ("create", "创建生成"),
    ("generate", "生成"), ("validate", "合规验证"),
    ("verify", "结果验证"), ("optimize", "可发现性优化"),
    ("score", "质量评分"), ("diagnose", "诊断分析"),
    ("treatment", "治疗实施"), ("retrospective", "复盘反哺"),
    ("feedback", "反馈闭环"), ("xv", "交叉验证"),
    ("coexistence", "共存检测"), ("dedup", "去重合并"),
    ("health", "健康治理"), ("lifecycle", "生命周期管理"),
    ("maturity", "成熟度评估"), ("coverage", "覆盖分析"),
    ("html", "可视化报告"), ("report", "报告生成"),
    ("adapt", "项目适配"), ("security", "安全审计"),
    ("taint", "污点追踪"), ("guard", "安全守卫"),
    ("discover", "可发现性优化"), ("trigger", "触发优化"),
    ("contract", "契约约束"), ("pipeline", "流水线编排"),
    ("rollback", "回滚保护"), ("snapshot", "快照管理"),
    ("pre_creation", "前置介入"), ("preintervention", "前置介入"),
]
def _declared_capability_labels(module: dict) -> set[str]:
    return {cap.strip() for cap in norm_entity_list(module.get("key_capabilities"))
            if isinstance(cap, str) and cap.strip()}
def _aggregate_capability_labels(modules: list) -> set[str]:
    labels: set[str] = set()
    for mod in modules:
        labels |= _declared_capability_labels(mod)
        labels |= match_capability_labels(
            entity_names(norm_entity_list(mod.get("functions"))
                         + norm_entity_list(mod.get("classes"))),
            _FUNC_VERB_CAP_MAP)
    return labels
def render_capability_boundary(
        scan_result: dict, skill_name: str = _DEFAULT_SKILL_NAME,
        skill_type: str = _DEFAULT_SKILL_TYPE) -> str:
    lines_out = []
    modules = normalize_scan_modules(scan_result)
    label = one_line(skill_label(skill_name)).strip() or "本技能"
    can_do_set = _aggregate_capability_labels(modules)
    lines_out.append("## 技能能力边界")
    lines_out.append("")
    lines_out.append(f"> 明确 `{label}` 能做什么、不能做什么。"
                     "AI Agent 必须先核对此边界再决定是否加载。")
    lines_out.append("")
    lines_out.append("### 能做（In Scope）")
    lines_out.append("")
    if can_do_set:
        for cap in sorted(can_do_set):
            safe_cap = one_line(cap).strip()
            if safe_cap:
                lines_out.append(f"- {safe_cap}")
    else:
        _log.debug("render_capability_boundary: 能力标签聚合为空,使用技能名兜底文案")
        lines_out.append(f"- 执行 {label} 名称所暗示的核心任务")
    lines_out.append("")
    skill_key = as_lower_text(skill_type).strip() or "generic"
    if skill_key == "skill":
        skill_key = "skill-management"
    domain_key = DOMAIN_HINT_TO_TYPE_KEY.get(skill_key, skill_key)
    domain_key = resolve_domain_key(domain_key, DOMAIN_NEGATIVES) or "generic"
    domain_neg = DOMAIN_NEGATIVES.get(domain_key, DOMAIN_NEGATIVES["generic"])
    lines_out.append("### 不能做（Out of Scope）")
    lines_out.append("")
    for neg in domain_neg[:5]:
        lines_out.append(f"- {neg}")
    lines_out.append("- 与本技能明示能力边界外的通用任务（闲聊、系统操作、不相关领域的代码处理）")
    lines_out.append("- 跨技能职责簇的混合操作（应拆分为多技能协作，而非本技能单点处理）")
    lines_out.append("")
    return "\n".join(lines_out)
def render_module_responsibility_list(scan_result: dict) -> str:
    lines_out = []
    modules = normalize_scan_modules(scan_result)
    total = len(modules)
    lines_out.append("## 全部 .py 文件清单")
    lines_out.append("")
    lines_out.append(f"> 共 **{total}** 个 .py 文件，每个文件职责一句话。"
                     "AI Agent 可据此快速定位目标模块，再查「模块能力详解」获取接口。")
    lines_out.append("")
    lines_out.append("| # | 文件 | 行数 | 分类 | 职责（一句话） |")
    lines_out.append("|---|------|------|------|----------------|")
    for idx, mod in enumerate(modules, 1):
        path, lines, cat, purpose = _profile_table_cells(mod, 120)
        lines_out.append(f"| {idx} | `{path}` | {lines} | {cat} "
                         f"| {md_escape_cell(purpose)} |")
    lines_out.append("")
    return "\n".join(lines_out)
CATEGORY_SCENARIOS = {
    "核心引擎": "执行核心逻辑、初始化主要流程",
    "流程编排": "分阶段执行、任务编排或多阶段管道处理",
    "检测/诊断": "扫描、检测或诊断目标对象",
    "修复/清理": "修复问题、清理冗余内容或自动化重构",
    "构建/生成": "生成产出物、创建文件或初始化项目结构",
    "维护/巡检": "巡检状态、维护文档或检查一致性",
    "安全/守卫": "安全检查、门禁校验或危险操作拦截",
    "类型/数据模型": "类型定义、数据结构声明或 API 签名约束",
    "工具/辅助": "调用辅助函数、通用工具或字符串/路径处理",
    "测试": "运行测试、验证功能正确性或回归测试",
    "诊断/分析": "分析健康状态、调用关系、盲点或依赖",
    "治疗/反馈": "处理反馈、复盘改进或闭环优化",
    "可发现性/优化": "优化可发现性、扩展触发词或提升识别率",
    "脚本/执行": "通过 CLI 脚本执行或独立进程调用",
    "上下文/约束": "加载上下文、约束条件、契约定义或配置管理",
    "清理/共存": "清理旧内容、检测共存冲突或安全清理",
    "生命周期/健康": "健康评分、生命周期管理或成熟度评估",
    "技能文档": "文档创建、诊断、重构或匹配规则验证",
    "交叉验证": "多源仲裁、基线对比、冲突解决或变异测试",
    "报告/可视化": "报告生成或结果可视化",
    "适配/项目": "多项目类型适配、配置加载或框架支持",
    "前置介入": "创建阶段质量预检、架构建议或历史经验注入",
    "基础设施": "延迟导入、模块加载优化或底层支撑",
    "通用": "通用任务执行",
}
def _sentence_fragment(text: Any) -> str:
    return one_line(norm_text(text), 120).strip().strip("。；;，,、 ")
def _build_agent_trigger_info(path: str, purpose: str, key_caps: list, cat: str) -> str:
    name = one_line(module_stem(path)).strip()
    if not name:
        name = _UNNAMED_MODULE
    if name == '__init__':
        scenario = "引用该包的公开接口、查看包导出面或初始化包级状态"
    else:
        scenario = CATEGORY_SCENARIOS.get(cat, f"使用 `{name}` 相关能力")
    parts = [f"**Agent 调用时机**: 需要{scenario}时调用 `{name}`"]
    purpose_text = _sentence_fragment(purpose)
    if purpose_text and not purpose_text.startswith("提供: "):
        parts.append(f"，{purpose_text}")
    caps = [one_line(cap).strip() for cap in norm_entity_list(key_caps)
            if isinstance(cap, str)]
    caps = [cap for cap in caps if cap]
    if caps:
        parts.append(f"。核心能力: {'、'.join(caps)}")
    return "".join(parts) + "。"
_ENTRY_SKIP_SUBSTR = (
    "get_status", "get_maintenance", "get_info", "get_version",
    "get_config", "get_setting", "get_path", "get_dir",
    "_internal", "_helper", "_util", "_cache",
    "setup_logging", "configure", "init_logging",
    "_load", "_save", "_parse", "_format",
)
_MAX_ENTRIES_PER_CATEGORY = 8
_ENTRY_SKIP_TOKEN_RE = re.compile(
    r"(?<![a-z0-9])(?:is|has|should|can|print|log|debug|warn)(?![a-z0-9])")
_ENTRY_VERB_WEIGHTS = {
    "quick": 10, "run": 9, "execute": 9, "main": 9,
    "diag": 8, "scan": 8, "analyze": 8, "diagnose": 8,
    "detect": 8, "check": 8, "validate": 8, "verify": 8,
    "build": 8, "create": 8, "generate": 8, "scaffold": 8,
    "fix": 7, "repair": 7, "heal": 7, "resolve": 7,
    "refactor": 7, "clean": 7, "optimize": 7, "enhance": 7,
    "score": 6, "evaluate": 6, "rate": 6,
    "discover": 6, "trigger": 6, "search": 6,
}
_ENTRY_VERB_TOKEN_RE = re.compile(
    r"(?<![a-z0-9])(" + "|".join(
        sorted(_ENTRY_VERB_WEIGHTS, key=len, reverse=True)) + r")(?![a-z0-9])")
_SKIP_TERM_RE_CACHE: dict[str, re.Pattern] = {}
def _is_skip_term(name: str, term: str) -> bool:
    pattern = _SKIP_TERM_RE_CACHE.get(term)
    if pattern is None:
        pattern = re.compile(
            r"(?<![a-z0-9])(?:re)?" + re.escape(term) + r"(?![a-z0-9])")
        _SKIP_TERM_RE_CACHE[term] = pattern
    return bool(pattern.search(name))
def _is_entry_skip_name(fname: str) -> bool:
    normalized = _split_identifier_words(fname)
    return (any(_is_skip_term(normalized, skip) for skip in _ENTRY_SKIP_SUBSTR)
            or _ENTRY_SKIP_TOKEN_RE.search(normalized) is not None)
def _first_named_entity(entities: list) -> str:
    for entity in norm_entity_list(entities):
        name = entity_name(entity)
        if name:
            return name
    return ""
def _entry_weight(name: str) -> int:
    words = _split_identifier_words(name)
    return max((_ENTRY_VERB_WEIGHTS.get(m.group(1), 0)
                for m in _ENTRY_VERB_TOKEN_RE.finditer(words)),
               default=0)
def select_entry_func(funcs: list, path: str) -> str | None:
    candidates = [
        name
        for func in norm_entity_list(funcs)
        if (name := entity_name(func))
        and not _is_entry_skip_name(name)
    ]
    if candidates:
        return max(candidates, key=_entry_weight)
    fallback = _first_named_entity(funcs)
    if fallback:
        _log.debug("render_trigger_entrypoint_mapping: 模块 %s 入口函数全命中黑名单,兜底首个有名函数 %s", path, fallback)
        return fallback
    return None
def _entry_display(path: str, funcs: list, classes: list) -> str:
    entry_func = select_entry_func(funcs, path)
    if entry_func:
        return f"`{md_escape_cell(entry_func)}()`"
    entry_class = _first_named_entity(classes)
    if entry_class:
        return f"`{md_escape_cell(entry_class)}` 类"
    return "（无公开入口，作为常量/类型定义模块）"
def _collect_category_entries(modules: list) -> dict[str, list[tuple[str, str, str]]]:
    cat_entries: dict[str, list[tuple[str, str, str]]] = {}
    for mod in modules:
        cat = norm_text(mod.get("category")).strip() or "通用"
        path = norm_text(mod.get("path"))
        entry = _entry_display(path, norm_entity_list(mod.get("functions")),
                               norm_entity_list(mod.get("classes")))
        cat_entries.setdefault(cat, []).append(
            (path, entry, norm_text(mod.get("purpose"))))
    return cat_entries
def render_trigger_entrypoint_mapping(
        scan_result: dict, skill_name: str = _DEFAULT_SKILL_NAME) -> str:
    modules = normalize_scan_modules(scan_result)
    cat_entries = _collect_category_entries(modules)
    label = one_line(skill_label(skill_name)).strip() or "本技能"
    lines_out = []
    lines_out.append("## 触发场景与入口函数映射表")
    lines_out.append("")
    lines_out.append(f"> 用户意图 → 推荐入口函数/类的直接映射。"
                     f"AI Agent 据此可一步定位到 `{label}` 内的具体调用点。")
    lines_out.append("")
    lines_out.append("| 触发场景 | 入口函数/类 | 所在模块 | 用途说明 |")
    lines_out.append("|---------|------------|---------|---------|")
    for cat, entries in cat_entries.items():
        scenario = "通用任务执行" if cat == "通用" else cat
        if len(entries) > _MAX_ENTRIES_PER_CATEGORY:
            scenario = f"{scenario}（另有 {len(entries) - _MAX_ENTRIES_PER_CATEGORY} 个模块）"
        for path, entry, purpose in entries[:_MAX_ENTRIES_PER_CATEGORY]:
            purpose_short = one_line(purpose, 80)
            lines_out.append(f"| {md_escape_cell(scenario)} | {entry} | `{md_escape_cell(path)}` "
                             f"| {md_escape_cell(purpose_short)} |")
    lines_out.append("")
    lines_out.append("**使用方法**：先匹配用户意图到「触发场景」列，"
                     "再从「入口函数/类」列获取调用名，最后从「所在模块」列定位文件。")
    lines_out.append("")
    return "\n".join(lines_out)
def render_forced_workflow_constraints(
        skill_name: str = _DEFAULT_SKILL_NAME, pattern: str = "") -> str:
    label = one_line(skill_label(skill_name)).strip() or "本技能"
    pattern_text = one_line(norm_text(pattern)).strip()
    lines_out = []
    lines_out.append("## 强制工作流与约束")
    lines_out.append("")
    lines_out.append(f"> `{label}` 的入口、参数和返回契约以其源码及 docstring 为准。"
                     "以下仅给出不依赖特定项目实现的通用工作流与安全约束。")
    lines_out.append("")
    lines_out.append("### 通用工作流")
    lines_out.append("")
    lines_out.append("```")
    lines_out.append("1. 能力定位  — 通过「模块能力全景」和「触发场景映射表」定位目标模块")
    lines_out.append("2. 接口确认  — 核对函数签名、参数类型、返回结构及已声明的副作用")
    lines_out.append("3. 按需预检  — 仅当技能提供预检入口时，按其契约检查输入与运行条件")
    lines_out.append("4. 调用执行  — 按实际能力选择 Python API 或 CLI，并使用该入口真实支持的参数")
    lines_out.append("5. 结果验证  — 按实际返回契约检查结果，不预设 status、error 等固定字段")
    lines_out.append("6. 回归检查  — 修改代码后运行相关测试与导入冒烟，不扩大到无关测试")
    lines_out.append("```")
    lines_out.append("")
    lines_out.append("### 通用约束")
    lines_out.append("")
    lines_out.append("- **命名约束**: AgentSkill 名称采用 kebab-case（小写字母、数字和连字符），长度 2-64")
    lines_out.append("- **结构约束**: 技能必须含 `SKILL.md`；Python 可采用根包、扁平模块、`scripts/`、`src/` 或 PEP 420 布局，`__init__.py` 按包契约提供")
    lines_out.append("- **安全约束**: 不对不可信输入使用动态执行或不安全的 shell 调用；凭据不得硬编码或写入文档")
    lines_out.append("- **输出约束**: 遵循各公开入口已声明的返回契约；新增自动化入口宜提供结构化结果")
    lines_out.append("- **写入约束**: 有副作用的操作须明确写出；需要原子性或幂等性时由对应实现保证并验证")
    lines_out.append("- **错误约束**: 按公开契约传播或返回错误，不得用 blanket except 隐藏失败")
    lines_out.append("- **依赖约束**: 声明真实依赖；只有声明为可选的能力才允许在依赖缺失时降级")
    lines_out.append("")
    if pattern_text:
        lines_out.append(f"### 推荐设计模式: {pattern_text}")
        lines_out.append("")
        lines_out.append(f"本技能推断为 **{pattern_text}** 模式，应遵循该模式的结构约定。")
        lines_out.append("")
    return "\n".join(lines_out)

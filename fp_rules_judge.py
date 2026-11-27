from __future__ import annotations

import ast
import copy
import logging
import os
import re
import time
from collections.abc import Iterator, Mapping
from dataclasses import dataclass, field
from typing import Any, ClassVar

from jwsgj.diag_guard_state import (
    read_json_artifact,
    write_json_artifact,
)
from jwsgj.diag_shared_ast_nodes import iter_module_level_stmts
from jwsgj.diag_shared_source_core import (
    read_cached,
    read_source_cached,
)
from jwsgj.diag_shared_source_scan import (
    equiv_rule_ids,
)
from jwsgj.diag_types_normalize import (
    as_item_list,
    as_str,
    extract_finding_line,
    finding_file_key,
    finite_float_or_zero,
    is_pure_int,
    is_real_number,
    normalize_line_no,
    now_iso,
    parse_locator_file,
    parse_locator_line,
    severity_literal_from_rank,
)
from jwsgj.diag_types_vocab import (
    FMT_DATETIME,
    PARSE_DEGRADE_EXC,
    SEVERITY_RANK,
)
from jwsgj.log_config import locked_artifact, log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    fp_rules_path,
    fp_suppression_path,
    fp_tracker_path,
    fp_tracker_rules_path,
)
from jwsgj.runtime_scope import (
    collect_scan_py_files,
    is_test_file_path,
)

__all__ = [
    "DEFAULT_SEVERITY",
    "KNOWN_FP_RULES",
    "LINE_ZERO_WHITELIST",
    "PROJECT_SCOPED_FP_RULES",
    "SUPPRESSION_DEFAULT_MIN_SEVERITY",
    "TAINT_PATH_TRAVERSAL_RULES",
    "AlertContext",
    "FilterReport",
    "FilterResult",
    "HeuristicFilter",
    "SelfAuditAwareness",
    "SelfAuditConfig",
    "VerdictResult",
    "annotate_findings_with_fp_evidence",
    "apply_fp_downgrade",
    "check_self_audit_fp",
    "enhance_taint_with_confidence",
    "equiv_dedup_key",
    "extract_alert_context",
    "filter_alerts",
    "finding_line_no",
    "fp_rule_registered",
    "get_fp_rule_ids",
    "is_fp_rule",
    "is_known_fp",
    "is_static_fp_rule",
    "is_test_scoped_fp_rule",
    "load_cv_fp_suppression_rules",
    "load_cv_fp_tracker_rates",
    "load_fp_rules",
    "load_fp_tracker_rates",
    "load_historical_fp_rules",
    "map_bandit_severity",
    "norm_rule_key",
    "normalize_suppression_rule",
    "rules_of",
    "save_fp_rules",
    "suppression_min_severity",
]
logger = logging.getLogger(__name__)
_UNSCOPED_SKILL_DIR = ""
_UNRESOLVED_FILE_PATH = ""
_UNRESOLVED_FILE_MARKERS = frozenset({"?", "n/a"})
_DEFAULT_FINDING_LINE = 1
def _dynamic_fp_registered(rule_id: str, skill_dir: str) -> bool:
    if not skill_dir or not isinstance(rule_id, str):
        return False
    rule_key = rule_id.strip()
    if not rule_key:
        return False
    try:
        return any(
            is_fp_rule(skill_dir, rid) for rid in equiv_rule_ids(rule_key))
    except Exception as e:  # noqa: BLE001
        logger.debug(
            "fp_rules_judge.is_fp_rule 不可用，跳过动态固化误报检查: %s", e
        )
        return False
_REGISTER_CALL_RE = re.compile(r"\.register\(\s*(\w+)")
_METRIC_RULE_PREFIXES: tuple[str, ...] = (
    "D34",
    "D35",
    "D36",
    "D38",
    "D41",
    "POL-",
    "TM-",
)
KNOWN_FP_RULES: dict[str, str] = {
    'GF-11': '变量名别名建议，信息级，非真实代码缺陷',
    'SL-06': '__init__导出检查，信息级建议，非真实代码缺陷',
    'AI-06': '正常代码模式(约束定义/配置)，非真实代码缺陷',
    'SN-03': '正常代码或已有异常保护，误报',
    'HP-006': '信息级建议，非真实代码缺陷',
    'C11_duplicates': '信息级建议，非真实代码缺陷',
    'C18_default_duplication': '默认参数重复属配置漂移建议，信息级非功能缺陷',
    'AP-C18': '重复默认参数，信息级配置收敛建议',
    'C19_passthrough_layer': '纯转发层属结构建议，需结合架构意图人工判断',
    'AP-C19': '纯转发层，信息级结构提示（PF01 已覆盖单函数粒度）',
    'AP-C8': '信息级建议，非真实代码缺陷',
    'missing_annotations': '类型注解风格建议，非功能缺陷',
    'HP-003': '延迟填充设计(ALL_RULES=[])，intentional design',
    'C17_dynamic_import': '循环依赖解决方案(延迟导入)，intentional design',
    'lazy_import': '延迟导入设计模式(循环依赖解决方案)，intentional design',
    'mutable_global': '正常全局变量模式，非真实代码缺陷',
    'TY-01': '治疗状态信息，非代码缺陷',
    'GENERIC': '文件级发现(line=0)，fallback rule_id，非具体缺陷',
    '_UNKNOWN_RULE': '无规则标识检测结果',
    'all_consistency': '路径无法解析(?)，line=0，明显误报',
    'SE-20': 'compile()用于语法验证(不执行代码)，代码审计工具自身功能',
    'AI-01': '匹配到字符串字面量/注释文本，非真实隐藏os导入',
    'AI-04': 'git命令参数为内部生成(时间戳标签)，非用户输入注入',
    'GF-07': '匹配注释文本(# 属性赋值)，非真实正则替换副作用',
    'security_pattern': '桌面工具os.path.join操作，非Web应用路径穿越',
    'T18-NO-ASSERT': '测试无断言需具体测试改进，非源码缺陷',
    'full_import': '导入失败属环境依赖缺失(z3等)，非代码缺陷',
    'D21-CROSS-MODULE-ASSIGN': 'D21扫描器跨模块赋值检测产物，非代码缺陷',
    'D21-DYNAMIC-IMPORT': 'D21扫描器__import__检测，工具功能非缺陷',
    'D21-IMPORTLIB': 'D21扫描器importlib检测，延迟导入设计模式',
    'D21-INIT-SIDE-EFFECT': 'D21扫描器__init__副作用检测，信息级',
    'D21-SYS-MODULES': 'D21扫描器sys.modules操作检测，模块管理功能',
    'D35': '静默降级增强建议，每个try/except块产出一个建议，非实际降级',
    'D36': '度量检测器产物，非代码缺陷',
    'D41': '度量检测器产物，非代码缺陷',
    'D17-LEVEL-MISUSE': '日志级别建议，信息级非缺陷',
    'D17-ERROR-IN-LOOP': '循环内日志级别建议，信息级非缺陷',
    'TM-SURVIVED': '突变测试存活是测试质量信号，非代码缺陷',
    'POL-01': '代码污染分数，度量产物非缺陷',
    'A1-missing_docstring': '文档建议，非功能缺陷（同 missing_docstring 口径）',
    'A1-missing_all': '__all__ 导出契约建议，信息级非缺陷（项目可用 lazy_imports 登记可达性）',
    'A1-over_limit': '复杂度/行数度量，健康指标非可修复缺陷（同 SZ-01 口径）',
    'A1-symbol_conflict': '跨文件同名公开符号分属独立命名空间，Python 语义无冲突；真实遮蔽由单文件级 import_override 检测负责，本规则仅信息级',
    '门禁错误-D01': '函数内延迟导入是有意设计(SKILL.md 明示)，非门禁错误',
    'E1-hardcoded_secret': '变量名含 token(令牌计数)被误判为硬编码密钥',
    'E1-HARDCODED-CRED': '测试文件中的凭据样例(fixture/占位符)非生产硬编码凭据',
    'S102': 'diag_simulate_sandbox 沙箱模拟器受限 builtins 执行，代码审计工具自身功能(同 SE-20 口径)',
    'EX-SWALLOWED': 'raise 语句被误判为异常吞没(实际是抛出而非吞没)',
    'E1-sql_injection': 'table_name 来自 sqlite_master 查询(数据库内部表名)，非用户输入',
    'E1-path_traversal': '本地 CLI 审计工具路径来自函数参数/CLI/环境变量，非不可信输入',
    'TAINT-path_traversal': '本地 CLI 审计工具污点追踪路径穿越：sink 路径均由技能目录/内部状态/CLI 参数派生，同 E1-path_traversal 口径',
    'BLE001': '诊断工具 except Exception 后降级/记录日志是防御性设计，非盲目捕获',
    'SIM102': '可折叠 if 是 P3 风格偏好，嵌套 if 在守卫子句场景更清晰',
    'C2_lazy_import': '延迟导入是循环依赖解决方案，设计模式',
    'AP-C2': '延迟导入设计模式，非缺陷',
    'C4_regression': '异常退化是防御性编程模式，非缺陷',
    'AP-C4': '退化代码，防御性设计，信息级提示',
    'C6_circular': '循环依赖可能是合法架构模式或需人工谨慎判断，降级信息级提示，不作批量修复项',
    'AP-C6': '循环依赖，信息级提示，不作批量修复项',
    'C1_facade': '门面反模式，架构设计提示，信息级',
    'AP-C1': '门面反模式，架构设计提示，信息级',
    'C16_stubs': '存根函数检测，需具体分析非批量过滤',
    'AP-C16': '桩函数，可能为合法默认实现/接口占位，信息级提示',
    'C8_dead_code': '死代码检测，需具体分析',
    'AP-C17': '动态导入，延迟加载设计，信息级提示',
    'AP-C11': '重复代码建议，信息级',
    'conditional_import': '条件导入(try/except)是防御性设计',
    'HP-004': '字符串拼接构造路径建议，风格级',
    'HP-002': '异常吞没(pass)已在SN-03覆盖',
    'ARCH-001': '模块自导入检测产物，非缺陷',
    'module_level_call': '模块级调用检测，信息级',
    'shadowing_builtin': '命名规范建议，非功能缺陷',
    'string_concat_in_loop': '性能建议，非功能缺陷',
    'too_many_params': '已被SZ-01覆盖',
    'deep_nesting': '已被SZ-01覆盖',
    'SZ-01': '复杂度度量(文件/类过长/嵌套深)，健康指标非可修复缺陷',
    'D21_unicode_safety': '全角标点检测(仅代码token)，字符串/注释内合法，信息级',
    'naming_violation': '命名规范建议，非功能缺陷',
    'unused_import': '未使用导入，风格建议',
    'missing_docstring': '文档建议，非功能缺陷',
    'empty_test_file': '测试质量建议，非源码缺陷',
    'GF-03': '重复语句，风格建议',
    'GF-04': 'lazy标记验证，信息级',
    'H01': '_前缀私有名 import * 问题，项目以 __all__ 管理导出不依赖 import *',
    'H02': '_前缀常量需显式导入，项目内部直接引用非 import *',
    'H08': '沙箱逃逸路径，diag_simulate/diag_runtime合法使用反射进行安全分析',
    'AI-05': '自定义find_class，安全检测器分析pickle反序列化，非真实漏洞',
    'CG-SIG-01': '签名不匹配，AST静态分析方法调用(self.method)vs函数调用参数计数误判',
    'danger_pattern': 'sys_exit/while_true/argparse_parse是CLI工具正常功能',
    'SE-03': '规则名称字符串常量(RULE_HARDCODED_CREDENTIAL)非真实凭据',
    'hardcoded_credential': '检测规则配置定义中的示例token/secret/password非真实凭据',
    'global_statement': 'global语句是模块级状态管理模式(缓存/注册表/校准器)，intentional design',
    'unbounded_recursion': 'check_*规则分发函数递归受规则集大小限制，非无界递归',
    'SE-18': 'assert用于开发时断言，项目不以-O模式运行，非生产验证依赖',
    'H05': '__init__含pass是抽象接口/run含docstring是占位符，非AI灌水代码',
    'SE-36': 'session_id是诊断会话ID非用户敏感数据，日志中记录会话ID是正常行为',
    'GF-01': '全角标点在注释/字符串中，非代码语法错误',
    'nested_loop': '嵌套循环在诊断工具中是正常的(遍历文件×遍历AST节点)，信息级',
    'data_flow_integrity': '数据流完整性度量，无具体定位，非代码缺陷',
    'H03': '异常降级返回空值是诊断工具标准实践(检查失败返回空结果不崩溃)，intentional design',
    'SN-05': 'debug级别日志用于非关键best-effort操作(write_audit/perf_trace等)，intentional design',
    'UNUSED-IMPORT': '未使用导入(P3),风格建议非功能缺陷',
    'DOC-01': 'SKILL.md缺失章节,文档结构建议非代码缺陷',
    'DC-01': '不可达语句(已降级P3)，AST 静态分析可能误判，修复删除语句会破坏控制流',
    'DC-02': '未使用导入(已降级P3)，可能被其他模块跨文件引用',
    'UC-01': '未使用导入模块(已降级P3)，单文件引用统计无法识别跨文件 re-export/动态引用',
    'SE-35': 'SE-35检测器自身的格式化代码，value是魔数检测值非用户输入，无注入风险',
    'GF-02': '全文未找到实际docstring断裂，检测器误报',
    'broad_except': '模块级可选导入降级+逐规则异常隔离，诊断工具标准设计模式',
    'empty_except': '测试fixture清理临时文件except OSError: pass，文件不存在时忽略是标准实践',
}
_DETECTOR_CODE_RULES: frozenset[str] = frozenset({
    'H01',
    'H02',
    'H08',
    'SE-18',
    'SE-20',
    'danger_pattern',
    'hardcoded_credential',
    'security_pattern',
    'data_flow_integrity',
    'GF-07',
    'SE-35',
    'GF-02',
})
_METRIC_PRODUCT_RULES: frozenset[str] = frozenset({
    "TY-01",
})
LINE_ZERO_WHITELIST: frozenset[str] = frozenset({
    "RUFF-F811", "RUFF-F401",
})
def _is_file_level_rule(rule_id: str) -> bool:
    return rule_id.startswith("A1-FILE-")
_DESIGN_PATTERN_RULES: frozenset[str] = frozenset({
    'global_statement',
    'unbounded_recursion',
    'HP-003',
    'HP-006',
    'lazy_import',
    'conditional_import',
    'mutable_global',
    'AP-C8',
    'full_import',
    'broad_except',
    'empty_except',
})
_STYLE_RULES: frozenset[str] = frozenset({
    "GF-01",
    "GF-03",
    "GF-04",
    "HP-002",
    "HP-004",
    "SL-06",
    "ARCH-001",
    "module_level_call",
    "shadowing_builtin",
    "string_concat_in_loop",
    "too_many_params",
    "deep_nesting",
    "naming_violation",
    "unused_import",
    "missing_docstring",
    "missing_annotations",
    "empty_test_file",
    "C8_dead_code",
    "nested_loop",
})
_SCAN_PRODUCT_RULES: frozenset[str] = frozenset({
    "GENERIC",
    "_UNKNOWN_RULE",
    "all_consistency",
    "T18-NO-ASSERT",
})
_UNKNOWN_FP_KEYWORDS: tuple[str, ...] = (
    "热点函数",
    "圈复杂度",
    "认知复杂度",
    "无任何调用者",
    "导入环",
    "hotspot function",
    "cyclomatic complexity",
    "cognitive complexity",
    "no callers",
    "no caller",
    "import cycle",
    "circular import",
    "unreferenced",
)
@dataclass
class FilterResult:
    is_fp: bool
    reason: str
    pattern: str
    confidence: float = 1.0
@dataclass
class SelfAuditConfig:
    enable_detector_code: bool = True
    enable_metric_product: bool = True
    enable_design_pattern: bool = True
    enable_style: bool = True
    enable_scan_product: bool = True
    enable_unknown_message: bool = True
    enable_dynamic_dispatch: bool = True
    enable_line_zero_filter: bool = True
    metric_rule_prefixes: tuple[str, ...] | None = None
def finding_line_no(item: Any) -> int:
    line = normalize_line_no(_field(item, "line", 0))
    if not line:
        line = normalize_line_no(_field(item, "line_number", 0))
    if line:
        return line
    try:
        if isinstance(item, dict):
            return max(0, extract_finding_line(item))
        return normalize_line_no(parse_locator_line(_field(item, "locator", "")))
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'finding_line_no:{type(e).__name__}')
        return 0
@dataclass(frozen=True)
class _FindingView:
    rule_id: str = ""
    file_path: str = ""
    message: str = ""
    line: int = 0
def _finding_file_path(item: Any) -> str:
    filepath = (_field(item, "file_path", "") or _field(item, "file", "")
                or _field(item, "filepath", ""))
    if not filepath:
        filepath = parse_locator_file(_field(item, "locator", ""))
    return str(filepath or "").strip()
def _finding_view(finding: dict[str, Any]) -> _FindingView:
    return _FindingView(
        rule_id=str(finding.get("rule_id") or "").strip(),
        file_path=_finding_file_path(finding),
        message=str(finding.get("message") or "").strip(),
        line=finding_line_no(finding),
    )
def _fp_result(pattern: str, reason: str, confidence: float) -> FilterResult:
    return FilterResult(
        is_fp=True, reason=reason, pattern=pattern, confidence=confidence)
@dataclass(frozen=True)
class _RuleFamily:
    pattern: str
    confidence: float
    reasons: Mapping[str, str]
    def judge(self, rule_id: str) -> FilterResult | None:
        reason = self.reasons.get(rule_id)
        if reason is None:
            return None
        return _fp_result(self.pattern, reason, self.confidence)
def _reason_family(pattern: str, confidence: float,
                   rules: frozenset[str]) -> _RuleFamily:
    return _RuleFamily(
        pattern=pattern,
        confidence=confidence,
        reasons={rule: KNOWN_FP_RULES[rule] for rule in rules},
    )
_DETECTOR_CODE_FAMILY = _reason_family(
    "detector_code", 0.95, _DETECTOR_CODE_RULES)
_DESIGN_PATTERN_FAMILY = _reason_family(
    "design_pattern", 0.90, _DESIGN_PATTERN_RULES)
_STYLE_FAMILY = _reason_family("style", 0.90, _STYLE_RULES)
_SCAN_PRODUCT_FAMILY = _reason_family("scan_product", 0.95, _SCAN_PRODUCT_RULES)
_METRIC_PRODUCT_FAMILY = _reason_family(
    "metric_product", 0.95, _METRIC_PRODUCT_RULES)
_MODE_CHECKS: tuple[tuple[str, str], ...] = (
    ("enable_detector_code", "_check_detector_code"),
    ("enable_metric_product", "_check_metric_product"),
    ("enable_design_pattern", "_check_design_pattern"),
    ("enable_style", "_check_style"),
    ("enable_scan_product", "_check_scan_product"),
    ("enable_unknown_message", "_check_unknown_message"),
    ("enable_dynamic_dispatch", "_check_dynamic_dispatch"),
    ("enable_line_zero_filter", "_check_line_zero"),
)
def _resolve_config_prefixes(
    value: tuple[str, ...] | str | None,
    default: tuple[str, ...],
) -> tuple[str, ...]:
    if value is None:
        return default
    if isinstance(value, (bytes, bytearray)):
        _decoded = _path_arg(value)
        if not _decoded:
            return default
        value = _decoded
    if isinstance(value, str):
        value = (value,)
    try:
        items = tuple(value)
    except TypeError as _e:
        log_swallowed(__name__, _e,
                      context='_resolve_config_prefixes:TypeError')
        return default
    return tuple(
        prefix for prefix in (str(item).strip() for item in items) if prefix)
def _read_source(path: str) -> str | None:
    content = read_cached(path)
    if content is None:
        logger.debug("源文件读取失败（按不可读降级）: %s", path)
    return content
def _path_arg(value: Any) -> str:
    if isinstance(value, os.PathLike):
        try:
            value = os.fspath(value)
        except TypeError as exc:
            log_swallowed(__name__, exc, context='_path_arg:TypeError')
            return ""
    if isinstance(value, (bytes, bytearray)):
        try:
            value = os.fsdecode(bytes(value))
        except (UnicodeDecodeError, TypeError) as exc:
            log_swallowed(__name__, exc, context='_path_arg:fsdecode')
            return ""
    return value.strip() if isinstance(value, str) else ""
def _source_file_names(skill_dir: str) -> list[str] | None:
    if not os.path.isdir(skill_dir):
        return None
    try:
        files = collect_scan_py_files(skill_dir)
    except OSError as e:
        logger.debug("源码枚举失败（按不可列举降级）: %s: %s", skill_dir, e)
        return None
    root = os.path.abspath(skill_dir)
    return sorted(
        os.path.relpath(path, root).replace(os.sep, "/")
        for path in files
    )
_LAZY_REGISTRY_BASENAMES = ("lazy_imports.py", "__init__.py")
def _registry_scan_order(names: list[str]) -> list[str]:
    selected = [
        name for name in names
        if name.rsplit("/", 1)[-1] in _LAZY_REGISTRY_BASENAMES
    ]
    return sorted(
        selected,
        key=lambda name: (
            _LAZY_REGISTRY_BASENAMES.index(name.rsplit("/", 1)[-1]),
            name.count("/"),
            name,
        ),
    )
_LAZY_TABLES_CACHE: dict[tuple, dict[str, str]] = {}
_LAZY_TABLES_CACHE_MAX = 64
def _load_lazy_tables(skill_dir: str) -> dict[str, str]:
    names = _registry_scan_order(_source_file_names(skill_dir) or [])
    cache_key = (skill_dir, _source_dir_fingerprint(skill_dir, names))
    cached = _LAZY_TABLES_CACHE.get(cache_key)
    if cached is not None:
        return dict(cached)
    table: dict[str, str] = {}
    complete = True
    for relative in names:
        if not _load_lazy_table_into(
                table, os.path.join(skill_dir, relative)):
            complete = False
    if complete:
        if len(_LAZY_TABLES_CACHE) >= _LAZY_TABLES_CACHE_MAX:
            _LAZY_TABLES_CACHE.clear()
        _LAZY_TABLES_CACHE[cache_key] = dict(table)
    return table
def _is_lazy_registry_assignment(
        node: ast.Assign | ast.AnnAssign, source_name: str) -> bool:
    if source_name.replace("\\", "/").rsplit("/", 1)[-1] != "__init__.py":
        return True
    targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
    for target in targets:
        if not isinstance(target, ast.Name):
            continue
        name = target.id.strip("_").casefold()
        if name == "composition_imports" or (
                "lazy" in name and name.endswith((
                    "import", "imports", "import_table", "import_map",
                    "registry", "registries", "registry_map",
                    "export", "exports", "export_table", "export_map",
                ))):
            return True
    return False
def _iter_lazy_pairs(
        tree: ast.AST, source_name: str = _UNRESOLVED_FILE_PATH,
) -> Iterator[tuple[str, str]]:
    for node in iter_module_level_stmts(tree):
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        if (not isinstance(node.value, ast.Dict)
                or not _is_lazy_registry_assignment(node, source_name)):
            continue
        value = node.value
        for k, v in zip(value.keys, value.values, strict=True):
            module_name = getattr(k, "value", None)
            if not isinstance(module_name, str):
                continue
            if not isinstance(v, ast.Tuple):
                continue
            for elt in v.elts:
                symbol = getattr(elt, "value", None)
                if isinstance(symbol, str):
                    yield symbol, module_name
def _load_lazy_table_into(table: dict[str, str], lazy_path: str) -> bool:
    if not os.path.isfile(lazy_path):
        return False
    content = _read_source(lazy_path)
    if content is None:
        return False
    try:
        tree = ast.parse(content)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("加载 lazy 登记表失败: %s", e)
        return True
    table.update(_iter_lazy_pairs(tree, lazy_path))
    return True
def _register_call_names(tree: ast.AST) -> set[str]:
    decorator_calls = {
        id(decorator)
        for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        for decorator in node.decorator_list
        if isinstance(decorator, ast.Call)
    }
    names: set[str] = set()
    for node in walk_nodes(tree):
        if (not isinstance(node, ast.Call) or id(node) in decorator_calls
                or not isinstance(node.func, ast.Attribute)
                or node.func.attr != "register" or not node.args):
            continue
        target = node.args[0]
        if isinstance(target, ast.Name):
            names.add(target.id)
        elif isinstance(target, ast.Attribute):
            names.add(target.attr)
    return names
def _decorator_register_names(tree: ast.AST) -> set[str]:
    return {
        node.name for node in walk_nodes(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and _decorated_by_register(node)
    }
_VISITOR_BASE_NAMES = frozenset({
    "NodeVisitor", "NodeTransformer", "CSTVisitor", "CSTTransformer",
})
def _visitor_dotted_name(node: ast.AST) -> str:
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        prefix = _visitor_dotted_name(node.value)
        return f"{prefix}.{node.attr}" if prefix else node.attr
    return ""
def _visitor_base_name(node: ast.AST) -> str:
    return _visitor_dotted_name(node).rsplit(".", 1)[-1]
def _visitor_module_file(
        module: str,
        source_name: str,
        level: int,
        source_files: frozenset[str],
) -> str:
    module_path = module.replace(".", "/") if module else ""
    if level:
        package = source_name.rsplit("/", 1)[0] if "/" in source_name else ""
        for _ in range(level - 1):
            if not package:
                return ""
            package = package.rsplit("/", 1)[0] if "/" in package else ""
        prefix = "/".join(part for part in (package, module_path) if part)
    else:
        prefix = module_path
    candidates = ((f"{prefix}.py", f"{prefix}/__init__.py") if prefix
                  else ("__init__.py",))
    return next((path for path in candidates if path in source_files), "")
def _visitor_import_bindings(
        tree: ast.AST,
        source_name: str,
        source_files: frozenset[str],
) -> tuple[dict[str, tuple[str, str]], list[str]]:
    bindings: dict[str, tuple[str, str]] = {}
    star_files: list[str] = []
    for node in iter_module_level_stmts(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                module_file = _visitor_module_file(
                    alias.name, source_name, 0, source_files)
                bindings[alias.asname or alias.name] = ("", module_file)
            continue
        if not isinstance(node, ast.ImportFrom):
            continue
        module = node.module or ""
        source_file = _visitor_module_file(
            module, source_name, node.level, source_files)
        for alias in node.names:
            if alias.name == "*":
                if source_file:
                    star_files.append(source_file)
                continue
            submodule = ".".join(part for part in (module, alias.name) if part)
            submodule_file = _visitor_module_file(
                submodule, source_name, node.level, source_files)
            class_key = f"{source_file}::{alias.name}" if source_file else ""
            if (not source_file and module in {"ast", "_ast", "libcst"}
                    and alias.name in _VISITOR_BASE_NAMES):
                class_key = alias.name
            bindings[alias.asname or alias.name] = (class_key, submodule_file)
    return bindings, star_files
def _qualify_visitor_base(
        base: ast.AST,
        source_name: str,
        local_classes: set[str],
        bindings: dict[str, tuple[str, str]],
        star_files: list[str],
) -> str:
    raw_name = _visitor_dotted_name(base)
    if not raw_name:
        return ""
    if "." not in raw_name and raw_name in local_classes:
        return f"{source_name}::{raw_name}"
    for key in sorted(bindings, key=len, reverse=True):
        if raw_name == key:
            class_key, _module_file = bindings[key]
            if class_key:
                return class_key
            break
        if raw_name.startswith(f"{key}."):
            _class_key, module_file = bindings[key]
            member = raw_name[len(key) + 1:]
            if module_file and member and "." not in member:
                return f"{module_file}::{member}"
            break
    base_name = _visitor_base_name(base)
    if base_name in _VISITOR_BASE_NAMES:
        return base_name
    if "." not in raw_name and len(star_files) == 1:
        return f"{star_files[0]}::{raw_name}"
    return raw_name
def _visitor_class_specs(
        tree: ast.AST,
        source_name: str = _UNRESOLVED_FILE_PATH,
        source_files: tuple[str, ...] = (),
) -> list[tuple[str, set[str], set[str]]]:
    available = frozenset(source_files)
    local_classes = {
        node.name for node in walk_nodes(tree) if isinstance(node, ast.ClassDef)}
    bindings, star_files = (_visitor_import_bindings(
        tree, source_name, available) if source_name else ({}, []))
    specs: list[tuple[str, set[str], set[str]]] = []
    for cls in walk_nodes(tree):
        if not isinstance(cls, ast.ClassDef):
            continue
        bases = ({_qualify_visitor_base(
            base, source_name, local_classes, bindings, star_files)
            for base in cls.bases} if source_name else {
                _visitor_base_name(base) for base in cls.bases})
        methods = {
            method.name for method in cls.body
            if isinstance(method, (ast.FunctionDef, ast.AsyncFunctionDef))
            and method.name.startswith(("visit_", "leave_"))
        }
        class_key = f"{source_name}::{cls.name}" if source_name else cls.name
        specs.append((class_key, bases, methods))
    return specs
def _visitor_method_names_from_specs(
        specs: list[tuple[str, set[str], set[str]]],
        source_name: str = _UNRESOLVED_FILE_PATH) -> set[str]:
    source_key = finding_file_key(source_name)
    visitor_classes: set[str] = set()
    visitor_definitions: set[int] = set()
    changed = True
    while changed:
        changed = False
        for index, (class_name, bases, _methods) in enumerate(specs):
            if index in visitor_definitions:
                continue
            if bases & (visitor_classes | _VISITOR_BASE_NAMES):
                visitor_definitions.add(index)
                if class_name not in visitor_classes:
                    visitor_classes.add(class_name)
                    changed = True
    return {
        method
        for index, (class_name, _bases, methods) in enumerate(specs)
        if index in visitor_definitions
        and (not source_key
             or finding_file_key(class_name.partition("::")[0]) == source_key)
        for method in methods
    }
def _dynamic_dispatch_details_of(
        content: str,
        source_name: str = _UNRESOLVED_FILE_PATH,
        source_files: tuple[str, ...] = (),
) -> tuple[set[str], list[tuple[str, set[str], set[str]]]]:
    try:
        tree = ast.parse(content)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("AST 解析失败（注册调用退回文本采集）: %s", e)
        return {m.group(1) for m in _REGISTER_CALL_RE.finditer(content)}, []
    registered = _register_call_names(tree) | _decorator_register_names(tree)
    return registered, _visitor_class_specs(tree, source_name, source_files)
_DISPATCH_FUNCS_CACHE: dict[tuple, tuple] = {}
_DISPATCH_FUNCS_CACHE_MAX = 64
def _source_dir_fingerprint(skill_dir: str, names: list[str]) -> tuple:
    fingerprint: list[tuple[str, int, int]] = []
    for name in names:
        try:
            _st = os.stat(os.path.join(skill_dir, name))
        except OSError as _swallow_e:
            log_swallowed(__name__, _swallow_e, context='_source_dir_fingerprint:OSError')
            fingerprint.append((name, -1, -1))
        else:
            fingerprint.append((name, _st.st_mtime_ns, _st.st_size))
    return tuple(sorted(fingerprint))
def _scan_dynamic_dispatch_funcs(
        skill_dir: str, source_name: str = _UNRESOLVED_FILE_PATH,
) -> tuple[set[str], set[str]]:
    names = _source_file_names(skill_dir) or []
    cache_key = (skill_dir, _source_dir_fingerprint(skill_dir, names))
    hit = _DISPATCH_FUNCS_CACHE.get(cache_key)
    if hit is not None:
        registered, visitors, registered_by_file, visitor_specs = hit
    else:
        registered: set[str] = set()
        registered_by_file: dict[str, frozenset[str]] = {}
        visitor_specs: list[tuple[str, set[str], set[str]]] = []
        complete = True
        for fname in names:
            content = _read_source(os.path.join(skill_dir, fname))
            if content is None:
                complete = False
                continue
            file_registered, file_specs = _dynamic_dispatch_details_of(
                content, fname, tuple(names))
            registered |= file_registered
            registered_by_file[finding_file_key(fname)] = frozenset(
                file_registered)
            visitor_specs.extend(file_specs)
        visitors = _visitor_method_names_from_specs(visitor_specs)
        if complete:
            if len(_DISPATCH_FUNCS_CACHE) >= _DISPATCH_FUNCS_CACHE_MAX:
                _DISPATCH_FUNCS_CACHE.clear()
            _DISPATCH_FUNCS_CACHE[cache_key] = (
                frozenset(registered), frozenset(visitors),
                registered_by_file, tuple(visitor_specs))
    if source_name:
        return (set(registered_by_file.get(finding_file_key(source_name), ())),
                _visitor_method_names_from_specs(
                    list(visitor_specs), source_name))
    return set(registered), set(visitors)
def _decorated_by_register(node: ast.FunctionDef | ast.AsyncFunctionDef) -> bool:
    for dec in node.decorator_list:
        target = dec.func if isinstance(dec, ast.Call) else dec
        if isinstance(target, ast.Attribute) and target.attr == "register":
            return True
        if isinstance(target, ast.Name) and target.id == "register":
            return True
    return False
_NEVER_CALLED_RES: tuple[re.Pattern[str], ...] = (
    re.compile(r"函数\s+[`'\"]?([^\s`'\"]+)[`'\"]?\s+定义了但从未被调用"),
    re.compile(
        r"(?:function|func)\s+[`'\"]?([A-Za-z_][\w.]*)[`'\"]?\s+"
        r"(?:is|was)\s+defined\s+but\s+(?:is\s+)?never\s+called",
        re.IGNORECASE,
    ),
    re.compile(
        r"[`'\"]?([A-Za-z_][\w.]*)[`'\"]?\s+(?:is|was)\s+defined\s+"
        r"but\s+(?:is\s+)?never\s+called",
        re.IGNORECASE,
    ),
)
_DISPATCH_CONFIDENCE = 0.95
def _never_called_func_name(message: str) -> str | None:
    for pattern in _NEVER_CALLED_RES:
        match = pattern.search(message)
        if match is not None:
            return match.group(1).rsplit(".", 1)[-1]
    return None
def _finding_source_name(skill_dir: str, file_path: str) -> str:
    path = _path_arg(file_path)
    if not path or not skill_dir:
        return ""
    candidate = path if os.path.isabs(path) else os.path.join(skill_dir, path)
    try:
        relative = os.path.relpath(os.path.abspath(candidate),
                                   os.path.abspath(skill_dir))
    except ValueError:
        return ""
    if (os.path.isabs(relative) or relative == os.pardir
            or relative.startswith(os.pardir + os.sep)):
        return ""
    return relative.replace(os.sep, "/")
def _lazy_module_matches_source(
        module_name: str, source_name: str, skill_dir: str,
) -> bool:
    if not source_name:
        return True
    module = module_name.strip() if isinstance(module_name, str) else ""
    if not module:
        return False
    package = os.path.basename(os.path.abspath(skill_dir))
    if module == package:
        module = ""
    elif package and module.startswith(package + "."):
        module = module[len(package) + 1:]
    prefix = module.replace(".", "/")
    candidates = ((f"{prefix}.py", f"{prefix}/__init__.py") if prefix
                  else ("__init__.py",))
    source_key = finding_file_key(source_name)
    return any(source_key == finding_file_key(candidate)
               for candidate in candidates)
class SelfAuditAwareness:
    def __init__(
        self,
        skill_dir: str = _UNSCOPED_SKILL_DIR,
        config: SelfAuditConfig | None = None,
    ) -> None:
        _dir = _path_arg(skill_dir)
        self.skill_dir = os.path.abspath(_dir) if _dir else ""
        self.config = config or SelfAuditConfig()
        self._is_self_audit: bool | None = None
        self._lazy_imports: dict[str, str] | None = None
        self._dispatch_funcs: set[str] | None = None
        self._visitor_funcs: set[str] | None = None
    @property
    def is_self_audit(self) -> bool:
        self._is_self_audit = self._detect_self_audit()
        return self._is_self_audit
    def check_finding(self, finding: dict[str, Any]) -> FilterResult:
        if not self.is_self_audit:
            return FilterResult(False, "", "invalid_project_context")
        if not isinstance(finding, dict):
            return FilterResult(
                False, "finding 非 dict 对象，跳过自审过滤", "invalid_finding")
        view = _finding_view(finding)
        for switch, checker in _MODE_CHECKS:
            if getattr(self.config, switch):
                result = getattr(self, checker)(view)
                if result:
                    return result
        return FilterResult(False, "", "no_match")
    def _detect_self_audit(self) -> bool:
        return bool(self.skill_dir) and os.path.isdir(self.skill_dir)
    def _check_detector_code(self, view: _FindingView) -> FilterResult | None:
        if (view.rule_id in PROJECT_SCOPED_FP_RULES
                and not _dynamic_fp_registered(
                    view.rule_id, self.skill_dir)):
            return None
        return _DETECTOR_CODE_FAMILY.judge(view.rule_id)
    def _check_metric_product(self, view: _FindingView) -> FilterResult | None:
        result = _METRIC_PRODUCT_FAMILY.judge(view.rule_id)
        if result is not None:
            return result
        prefixes = _resolve_config_prefixes(
            self.config.metric_rule_prefixes, _METRIC_RULE_PREFIXES)
        prefix = next(
            (p for p in prefixes if view.rule_id.startswith(p)), "")
        if not prefix:
            return None
        return _fp_result(
            "metric_product",
            f"度量产物规则前缀 {prefix}，{view.rule_id} 是度量指标非代码缺陷",
            0.90,
        )
    def _check_design_pattern(self, view: _FindingView) -> FilterResult | None:
        if (view.rule_id in PROJECT_SCOPED_FP_RULES
                and not _dynamic_fp_registered(
                    view.rule_id, self.skill_dir)):
            return None
        return _DESIGN_PATTERN_FAMILY.judge(view.rule_id)
    def _check_style(self, view: _FindingView) -> FilterResult | None:
        if (view.rule_id in PROJECT_SCOPED_FP_RULES
                and not _dynamic_fp_registered(
                    view.rule_id, self.skill_dir)):
            return None
        return _STYLE_FAMILY.judge(view.rule_id)
    def _check_scan_product(self, view: _FindingView) -> FilterResult | None:
        result = _SCAN_PRODUCT_FAMILY.judge(view.rule_id)
        if result is not None:
            return result
        reason = _symbol_trace_fp_reason(view.rule_id, view.message)
        if reason:
            return _fp_result("scan_product", reason, 0.95)
        return None
    def _check_unknown_message(self, view: _FindingView) -> FilterResult | None:
        if (view.rule_id != "unknown"
                or not _dynamic_fp_registered(
                    view.rule_id, self.skill_dir)):
            return None
        message_folded = view.message.casefold()
        for keyword in _UNKNOWN_FP_KEYWORDS:
            if keyword.casefold() in message_folded:
                return _fp_result(
                    "unknown_message",
                    f"unknown规则消息匹配'{keyword}'，度量/动态分发产物非代码缺陷",
                    0.90,
                )
        return None
    def _check_dynamic_dispatch(self, view: _FindingView) -> FilterResult | None:
        if view.rule_id != "unknown":
            return None
        func_name = _never_called_func_name(view.message)
        if func_name is None:
            return None
        source_name = _finding_source_name(self.skill_dir, view.file_path)
        if not source_name:
            return None
        reason = self._dispatch_reason(func_name, source_name)
        if reason is None:
            return None
        return _fp_result("dynamic_dispatch", reason, _DISPATCH_CONFIDENCE)
    def _dispatch_reason(
            self, func_name: str, source_name: str = _UNRESOLVED_FILE_PATH,
    ) -> str | None:
        lazy_module = self._get_lazy_imports().get(func_name)
        if (lazy_module is not None and _lazy_module_matches_source(
                lazy_module, source_name, self.skill_dir)):
            return f"函数 {func_name} 通过延迟导入注册表分发(lazy 登记表)，非死代码"
        if func_name in self._get_visitor_funcs(source_name):
            return f"函数 {func_name} 是 Visitor/Transformer 方法，由访问者框架动态分发"
        if func_name in self._get_dispatch_funcs(source_name):
            return (f"函数 {func_name} 通过注册表登记后被动态分发调用，"
                    "非死代码")
        return None
    def _check_line_zero(self, view: _FindingView) -> FilterResult | None:
        if not _dynamic_fp_registered(view.rule_id, self.skill_dir):
            return None
        if (view.line == 0
                and view.rule_id not in LINE_ZERO_WHITELIST
                and not _is_file_level_rule(view.rule_id)):
            return _fp_result(
                "line_zero",
                f"文件级发现(line=0)，{view.rule_id}无具体行号定位",
                0.85,
            )
        if (not view.file_path
                or view.file_path.strip().casefold()
                in _UNRESOLVED_FILE_MARKERS):
            return _fp_result(
                "path_unresolved",
                f"路径无法解析，{view.rule_id}无法定位文件",
                0.85,
            )
        return None
    def _get_lazy_imports(self) -> dict[str, str]:
        self._lazy_imports = _load_lazy_tables(self.skill_dir)
        return self._lazy_imports
    def _get_dispatch_funcs(
            self, source_name: str = _UNRESOLVED_FILE_PATH) -> set[str]:
        self._dispatch_funcs, self._visitor_funcs = (
            _scan_dynamic_dispatch_funcs(self.skill_dir, source_name))
        return self._dispatch_funcs
    def _get_visitor_funcs(
            self, source_name: str = _UNRESOLVED_FILE_PATH) -> set[str]:
        self._dispatch_funcs, self._visitor_funcs = (
            _scan_dynamic_dispatch_funcs(self.skill_dir, source_name))
        return self._visitor_funcs
    def check_findings(
        self, findings: list[dict]
    ) -> tuple[list[dict], list[dict]]:
        fp_list: list[dict] = []
        real_list: list[dict] = []
        if findings is None:
            return fp_list, real_list
        if not isinstance(findings, (list, tuple)):
            findings = [findings]
        for finding in findings:
            if not isinstance(finding, dict):
                logger.warning(
                    "check_findings: 跳过非 dict 发现(%s)",
                    type(finding).__name__)
                continue
            result = self.check_finding(finding)
            if result.is_fp:
                finding["_saa_pattern"] = result.pattern
                finding["_saa_reason"] = result.reason
                fp_list.append(finding)
            else:
                real_list.append(finding)
        return fp_list, real_list
    def get_stats(self) -> dict:
        return {
            "is_self_audit": self.is_self_audit,
            "skill_dir": self.skill_dir,
            "metric_rule_prefixes": list(_resolve_config_prefixes(
                self.config.metric_rule_prefixes, _METRIC_RULE_PREFIXES)),
            "detector_code_rules": len(_DETECTOR_CODE_FAMILY.reasons),
            "metric_product_rules": len(_METRIC_PRODUCT_FAMILY.reasons),
            "design_pattern_rules": len(_DESIGN_PATTERN_FAMILY.reasons),
            "style_rules": len(_STYLE_FAMILY.reasons),
            "scan_product_rules": len(_SCAN_PRODUCT_FAMILY.reasons),
        }
_DEFAULT_SAA_CACHE: dict[str, SelfAuditAwareness] = {}
_DEFAULT_SAA_CACHE_MAX = 32
def _default_self_audit_awareness(skill_dir: str) -> SelfAuditAwareness:
    _dir = _path_arg(skill_dir)
    key = os.path.abspath(_dir) if _dir else ""
    saa = _DEFAULT_SAA_CACHE.get(key)
    if saa is None:
        if len(_DEFAULT_SAA_CACHE) >= _DEFAULT_SAA_CACHE_MAX:
            _DEFAULT_SAA_CACHE.clear()
        saa = SelfAuditAwareness(skill_dir)
        _DEFAULT_SAA_CACHE[key] = saa
    return saa
def check_self_audit_fp(
    finding: dict,
    skill_dir: str = _UNSCOPED_SKILL_DIR,
    config: SelfAuditConfig | None = None,
) -> tuple[bool, str]:
    saa = (_default_self_audit_awareness(skill_dir) if config is None
           else SelfAuditAwareness(skill_dir, config))
    result = saa.check_finding(finding)
    if result.is_fp:
        return True, f"[自审感知:{result.pattern}] {result.reason}"
    return False, ""
def _fp_by_self_audit(item: dict, skill_dir: str) -> tuple[bool, str]:
    if not skill_dir:
        return False, ""
    try:
        return check_self_audit_fp(item, skill_dir)
    except Exception as e:  # noqa: BLE001
        logger.debug("self_audit_awareness 不可用，跳过自审感知检查: %s", e)
    return False, ""
def norm_rule_key(value) -> str:
    return as_str(value).strip()
def _fp_by_rule_sources(item: dict, rule_id: str,
                        skill_dir: str) -> tuple[bool, str]:
    _file = _finding_file_path(item)
    if is_test_scoped_fp_rule(rule_id) and not is_test_file_path(_file):
        return False, ""
    if _dynamic_fp_registered(rule_id, skill_dir):
        return True, f"{rule_id}动态固化误报规则"
    is_fp, reason = _fp_by_self_audit(item, skill_dir)
    if is_fp:
        return True, reason
    known_reason = KNOWN_FP_RULES.get(rule_id)
    if known_reason is not None:
        if not _fp_rule_in_scope(rule_id, skill_dir, _file):
            return False, ""
        return True, known_reason
    return False, ""
_EMPTY_TRACE_RE = re.compile(
    r"\b\d+\s+steps?\s*,\s*0\s+constraints?\b", re.IGNORECASE)
def _symbol_trace_fp_reason(rule_id: str, message: str) -> str:
    if not rule_id.startswith("SYM-") or not _EMPTY_TRACE_RE.search(message):
        return ""
    if rule_id.startswith("SYM-cfsp_"):
        return "跨文件符号执行trace无实际发现(0 constraints)，非代码缺陷"
    return "单步无约束参数回溯trace，无跨文件污点传播，非代码缺陷"
def is_known_fp(
        item: dict, skill_dir: str = _UNSCOPED_SKILL_DIR
) -> tuple[bool, str]:
    if not isinstance(item, dict):
        return False, ""
    rule_id = norm_rule_key(item.get("rule_id", ""))
    is_fp, reason = _fp_by_rule_sources(item, rule_id, skill_dir)
    if not is_fp:
        reason = _symbol_trace_fp_reason(rule_id, as_str(item.get("message")))
        is_fp = bool(reason)
    if is_fp:
        return True, reason
    return False, ""
def _sev_rank_of(sev: str) -> int | None:
    try:
        return SEVERITY_RANK.get(str(sev).upper().strip())
    except Exception as _e:  # noqa: BLE001
        log_swallowed(__name__, _e,
                      context=f'_sev_rank_of:{type(_e).__name__}')
        return None
def _suppression_rank_ladder(fp_rate: float, fp_count: int) -> int:
    rate = finite_float_or_zero(fp_rate)
    count = finite_float_or_zero(fp_count)
    if rate >= 0.95 and count >= 50:
        return 2
    if rate >= 0.80 and count >= 20:
        return 3
    return 4
def suppression_min_severity(fp_rate: float, fp_count: int,
                             severities=None) -> str:
    target_rank = _suppression_rank_ladder(fp_rate, fp_count)
    if isinstance(severities, str):
        observed = [severities]
    elif isinstance(severities, (list, tuple, set, frozenset, dict)):
        observed = list(severities)
    elif severities is None:
        observed = []
    else:
        observed = [severities]
    sev_ranks = [r for r in (
        _sev_rank_of(s) for s in observed
    ) if r is not None]
    if sev_ranks:
        target_rank = min(target_rank, min(sev_ranks))
    target_rank = max(2, target_rank)
    return severity_literal_from_rank(target_rank)
def _fp_evidence_payload(*, is_false_positive: bool, confidence: float,
                         evidence: list, reasoning: str) -> dict:
    return {
        "is_false_positive": is_false_positive,
        "confidence": confidence,
        "evidence": list(evidence),
        "reasoning": reasoning,
    }
@dataclass
class VerdictResult:
    is_false_positive: bool = False
    confidence: float = 0.5
    reasoning: str = ""
    evidence: list[str] = field(default_factory=list)
    framework_defense: bool = False
    sanitizer: bool = False
    alert_id: str = ""
@dataclass
class FilterReport:
    total_alerts: int = 0
    filtered_alerts: list = field(default_factory=list)
    details: list = field(default_factory=list)
@dataclass
class AlertContext:
    alert_id: str = ""
    rule_id: str = ""
    rule_category: str = ""
    severity: str = ""
    file_path: str = ""
    line_number: int = _DEFAULT_FINDING_LINE
    code_snippet: str = ""
    function_context: str = ""
    class_context: str = ""
class HeuristicFilter:
    STRONG_SANITIZERS: ClassVar[list] = [
        (r'html\.escape\(', 'HTML转义'),
        (r'shlex\.quote\(', 'Shell引号转义'),
        (r're\.escape\(', '正则转义'),
        (r'escape_string\(', 'SQL转义'),
        (r'int\(\s*\w+\s*\)', '整数强制转换'),
        (r'ast\.literal_eval\(', 'AST安全字面量'),
        (r'\.filter\(\w+=\w+\)', 'Django ORM参数化过滤'),
        (r'\.execute\(\s*[\'"].*?%s', '参数化SQL (占位符)'),
        (r'@login_required', 'Django登录装饰器'),
        (r'@permission_required', 'Django权限装饰器'),
        (r'request\.user\.is_authenticated', '用户认证检查'),
    ]
    TEST_PATTERNS: ClassVar[list] = [
        (r'test_\w+\.py', '单元测试文件'),
        (r'def test_', '测试函数'),
        (r'unittest\.', 'unittest框架'),
        (r'pytest', 'pytest框架'),
        (r'if __name__ == [\'"]__main__[\'"]', '脚本入口'),
    ]
    SAFE_CONTEXTS: ClassVar[list] = [
        (r'@app\.route.*methods=\[[\'"]GET[\'"]', 'GET-only路由 (XSS/注入风险低)'),
        (r'\.objects\.filter\(', 'Django ORM安全查询'),
        (r'Model\.objects\.get\(', 'Django安全获取'),
        (r'subprocess\.run\(.*shell=False', 'subprocess shell=False'),
        (r'\.execute\(.*\?', 'SQLite参数化查询'),
    ]
    _IDENT_GUARD: ClassVar[str] = r"(?<!\w)"
    @classmethod
    def _evidence_hit(cls, pattern: str, text: str) -> bool:
        if not pattern:
            return False
        if pattern[0].isalpha() or pattern[0] == "_":
            pattern = cls._IDENT_GUARD + pattern
        return re.search(pattern, text) is not None
    @classmethod
    def _collect_channel(cls, ctx: AlertContext, patterns: list,
                         fields: tuple, label: str,
                         hits: list[str]) -> bool:
        text = "\n".join(
            str(getattr(ctx, name) or "") for name in fields)
        hit = False
        for pattern, desc in patterns:
            if cls._evidence_hit(pattern, text):
                hits.append(f"{label}{desc}")
                hit = True
        return hit
    @classmethod
    def evaluate(cls, ctx: AlertContext) -> VerdictResult:
        evidence_fp: list[str] = []
        sanitizer_hit = cls._collect_channel(
            ctx, cls.STRONG_SANITIZERS, ("function_context", "code_snippet"),
            "检测到净化器: ", evidence_fp)
        cls._collect_channel(
            ctx, cls.TEST_PATTERNS, ("file_path", "function_context"),
            "测试/脚本代码: ", evidence_fp)
        defense_hit = cls._collect_channel(
            ctx, cls.SAFE_CONTEXTS, ("function_context",),
            "安全上下文: ", evidence_fp)
        is_fp = ((sanitizer_hit or defense_hit)
                 and len(evidence_fp) >= 2)
        confidence = min(0.95, len(evidence_fp) * 0.30) if is_fp else 0.5
        reasoning = ("；".join(evidence_fp) if evidence_fp
                     else "无净化器/测试/安全上下文证据")
        return VerdictResult(
            is_false_positive=is_fp,
            confidence=confidence,
            evidence=evidence_fp,
            reasoning=reasoning,
            sanitizer=sanitizer_hit,
            framework_defense=defense_hit,
        )
def _decorated_decl_span(node) -> tuple[int, int]:
    start = node.lineno
    if node.decorator_list:
        start = min(start, node.decorator_list[0].lineno)
    return start, node.end_lineno or node.lineno
def _narrowest_enclosing_decl(
        tree: ast.AST, target_lineno: int,
        types: tuple[type, ...]) -> tuple[Any, int, int] | None:
    best: tuple[Any, int, int] | None = None
    for node in walk_nodes(tree):
        if not isinstance(node, types):
            continue
        start, end = _decorated_decl_span(node)
        if (start <= target_lineno <= end
                and (best is None
                     or (end - start) < (best[2] - best[1]))):
            best = (node, start, end)
    return best
def _find_enclosing_function_span(tree: ast.AST,
                                   target_lineno: int) -> tuple[int, int] | None:
    hit = _narrowest_enclosing_decl(
        tree, target_lineno, (ast.FunctionDef, ast.AsyncFunctionDef))
    return (hit[1], hit[2]) if hit else None
def _find_enclosing_class_name(tree: ast.AST,
                                target_lineno: int) -> str | None:
    hit = _narrowest_enclosing_decl(tree, target_lineno, (ast.ClassDef,))
    return hit[0].name if hit else None
def _field(item: Any, key: str, default: Any = None) -> Any:
    if isinstance(item, dict):
        return item.get(key, default)
    return getattr(item, key, default)
def _coerce_lineno(raw: Any) -> int:
    try:
        return int(raw or _DEFAULT_FINDING_LINE)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e,
                      context=f'_coerce_lineno:{type(_e).__name__}')
        return _DEFAULT_FINDING_LINE
def _read_alert_source(filepath: str) -> str | None:
    source = read_source_cached(filepath)
    if source is None:
        logger.warning("_read_alert_source: 无法读取 %s（解释器同口径）", filepath)
    return source
def _context_snippet(lines: list[str], line_number: int) -> str:
    idx = line_number - 1
    if idx >= len(lines):
        return ""
    return "\n".join(lines[max(0, idx - 5):idx + 6])
def _parse_alert_tree(source: str) -> ast.AST | None:
    try:
        return ast.parse(source)
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e, context='extract_alert_context:SyntaxError')
        return None
def _context_bodies(tree: ast.AST, lines: list[str],
                    line_number: int) -> tuple[str, str]:
    span = _find_enclosing_function_span(tree, line_number)
    fn_body = "\n".join(lines[span[0] - 1:span[1]]) if span else ""
    return fn_body, _find_enclosing_class_name(tree, line_number) or ""
def extract_alert_context(filepath: str,
                          line_number: int = _DEFAULT_FINDING_LINE,
                          source: str | None = None) -> AlertContext:
    raw_filepath = filepath
    filepath = _path_arg(filepath)
    ctx = AlertContext(
        file_path=filepath,
        line_number=max(_DEFAULT_FINDING_LINE, _coerce_lineno(line_number)))
    if source is None:
        if not filepath:
            logger.debug("extract_alert_context: 告警文件路径非法(%s)，按无上下文降级",
                         type(raw_filepath).__name__)
            return ctx
        source = _read_alert_source(filepath)
        if source is None:
            return ctx
    lines = source.split("\n")
    ctx.code_snippet = _context_snippet(lines, ctx.line_number)
    tree = _parse_alert_tree(source)
    if tree is not None:
        ctx.function_context, ctx.class_context = _context_bodies(
            tree, lines, ctx.line_number)
    return ctx
def _extract_path_line(item: object) -> tuple[str, int]:
    return (_finding_file_path(item),
            max(_DEFAULT_FINDING_LINE, finding_line_no(item)))
def _source_map_of(source_map: Any) -> dict[str, str]:
    if not isinstance(source_map, Mapping):
        return {}
    return {str(key): value for key, value in source_map.items()
            if isinstance(value, str)}
def _source_of(source_map: Mapping, filepath: str) -> str | None:
    source = source_map.get(filepath)
    return source if isinstance(source, str) else None
def _build_alert_context(item: object,
                          source_map: Mapping) -> AlertContext:
    filepath, lineno = _extract_path_line(item)
    if filepath:
        return extract_alert_context(
            filepath, lineno, source=_source_of(source_map, filepath))
    return AlertContext(line_number=lineno)
def _alert_ctx(alert: dict, source_map: Mapping) -> AlertContext:
    ctx = _build_alert_context(alert, source_map)
    ctx.alert_id = str(alert.get("id") or alert.get("rule_id") or "")
    ctx.rule_id = str(alert.get("rule_id") or "")
    ctx.rule_category = str(
        alert.get("category") or alert.get("rule_category") or "")
    ctx.severity = str(alert.get("severity") or "P1")
    return ctx
def filter_alerts(alerts: list[dict],
                  source_map: dict[str, str] | None = None) -> FilterReport:
    source_map = _source_map_of(source_map)
    items = as_item_list(alerts, log_tag="filter_alerts")
    report = FilterReport(total_alerts=len(items))
    for alert in items:
        if not isinstance(alert, dict):
            continue
        ctx = _alert_ctx(alert, source_map)
        verdict = HeuristicFilter.evaluate(ctx)
        verdict.alert_id = ctx.alert_id
        report.details.append(verdict)
        if verdict.is_false_positive:
            report.filtered_alerts.append(alert)
    return report
def enhance_taint_with_confidence(taint_flows: list,
                                  source_map: dict[str, str] | None = None) -> list[dict]:
    source_map = _source_map_of(source_map)
    enhanced: list[dict] = []
    flows = as_item_list(taint_flows, log_tag="enhance_taint_with_confidence")
    for flow in flows:
        ctx = _build_alert_context(flow, source_map)
        verdict = HeuristicFilter.evaluate(ctx)
        enhanced.append({
            "flow": flow,
            "confidence": verdict.confidence,
            "is_false_positive": verdict.is_false_positive,
            "reasoning": verdict.reasoning,
            "evidence": list(verdict.evidence),
            "fp_evidence": _fp_evidence_payload(
                is_false_positive=verdict.is_false_positive,
                confidence=verdict.confidence,
                evidence=verdict.evidence,
                reasoning=verdict.reasoning),
        })
    return enhanced
def annotate_findings_with_fp_evidence(findings: list,
                                        source_map: dict[str, str] | None = None) -> int:
    source_map = _source_map_of(source_map)
    items = as_item_list(findings, log_tag="annotate_findings_with_fp_evidence")
    return sum(_annotate_one(finding, source_map) for finding in items)
def _annotate_one(finding: Any, source_map: Mapping) -> int:
    filepath, lineno = _extract_path_line(finding)
    if not filepath:
        return 0
    verdict = HeuristicFilter.evaluate(
        extract_alert_context(
            filepath, lineno, source=_source_of(source_map, filepath)))
    payload = _fp_evidence_payload(
        is_false_positive=verdict.is_false_positive,
        confidence=verdict.confidence,
        evidence=verdict.evidence,
        reasoning=verdict.reasoning)
    try:
        if isinstance(finding, dict):
            finding["fp_evidence"] = payload
        else:
            finding.fp_evidence = payload
    except (AttributeError, TypeError) as e:
        logger.debug("降级容错路径触发（静默留痕）: %s", e)
        return 0
    return 1 if verdict.is_false_positive else 0
DEFAULT_SEVERITY = "P3"
_P_SEV_PREFIX_RE = re.compile(r"^P([0-4])(?![0-9])", re.IGNORECASE)
_HIGH_SEVERITY_ALIASES: frozenset[str] = frozenset({"HIGH", "BLOCK"})
def _severity_core(severity) -> str:
    sev_str = str(severity).strip()
    m = _P_SEV_PREFIX_RE.match(sev_str)
    return "P" + m.group(1) if m else sev_str.upper()
def _str_rule_key(rule_id):
    return rule_id.strip() if isinstance(rule_id, str) else None
TAINT_PATH_TRAVERSAL_RULES: frozenset[str] = frozenset({
    "TAINT-path_traversal",
    "E1-path_traversal",
})
PROJECT_SCOPED_FP_RULES: frozenset[str] = frozenset({
    "A1-missing_all",
    "AI-04",
    "danger_pattern",
    "门禁错误-D01",
    "E1-sql_injection",
    "E1-path_traversal",
    "TAINT-path_traversal",
    "S102",
    "BLE001",
    "H01",
    "H02",
    "H08",
    "AI-05",
    "SE-03",
    "SE-18",
    "SE-20",
    "SE-36",
    "hardcoded_credential",
    "global_statement",
    "unbounded_recursion",
    "nested_loop",
    "H03",
    "SN-05",
    "full_import",
    "security_pattern",
    "D21-CROSS-MODULE-ASSIGN",
    "D21-DYNAMIC-IMPORT",
    "D21-IMPORTLIB",
    "D21-INIT-SIDE-EFFECT",
    "D21-SYS-MODULES",
})
def _static_fp_rule_registered(
        rule_key: str, skill_dir: str = _UNSCOPED_SKILL_DIR) -> bool:
    known_key = rule_key
    if known_key not in KNOWN_FP_RULES:
        known_key = next(
            (rid for rid in sorted(equiv_rule_ids(rule_key))
             if rid in KNOWN_FP_RULES), "")
    if not known_key:
        return False
    if known_key in PROJECT_SCOPED_FP_RULES:
        return _dynamic_fp_registered(rule_key, skill_dir)
    return True
def _fp_rule_in_scope(
        rule_key: str, skill_dir: str = _UNSCOPED_SKILL_DIR,
        file_path: str = _UNRESOLVED_FILE_PATH) -> bool:
    if not _static_fp_rule_registered(rule_key, skill_dir):
        return False
    if is_test_scoped_fp_rule(rule_key):
        return is_test_file_path(file_path)
    return True
def apply_fp_downgrade(rule_id: str | None, severity: str | None,
                       *, skill_dir: str = _UNSCOPED_SKILL_DIR,
                       file_path: str = _UNRESOLVED_FILE_PATH) -> str | None:
    if not severity:
        return severity
    rule_key = _str_rule_key(rule_id)
    core = _severity_core(severity)
    rank = 0 if core in _HIGH_SEVERITY_ALIASES else _sev_rank_of(core)
    if rank is None:
        return DEFAULT_SEVERITY
    if (rule_key and rank <= 2
            and _fp_rule_in_scope(rule_key, skill_dir, file_path)):
        return DEFAULT_SEVERITY
    return severity_literal_from_rank(rank)
def is_static_fp_rule(
        rule_id: str, *, skill_dir: str = _UNSCOPED_SKILL_DIR,
        file_path: str = _UNRESOLVED_FILE_PATH) -> bool:
    key = _str_rule_key(rule_id)
    return key is not None and _fp_rule_in_scope(key, skill_dir, file_path)
_BANDIT_SEVERITY_MAP = {
    "CRITICAL": "P0", "HIGH": "P0", "MEDIUM": "P1", "LOW": "P2",
}
_BANDIT_SEVERITY_DEFAULT = "P2"
def map_bandit_severity(severity: str) -> str:
    return _BANDIT_SEVERITY_MAP.get(str(severity or "").strip().upper(),
                                    _BANDIT_SEVERITY_DEFAULT)
_TEST_SCOPED_FP_RULES = frozenset({"E1-hardcoded_secret", "E1-HARDCODED-CRED"})
def is_test_scoped_fp_rule(rule_id: str) -> bool:
    key = _str_rule_key(rule_id)
    return key is not None and key in _TEST_SCOPED_FP_RULES
_FP_RULES_CACHE: dict[str, tuple[tuple[float, int], dict]] = {}
_FP_RULES_CACHE_MAX = 64
def _read_rule_store(path: str, label: str) -> dict | None:
    data, kind, err = read_json_artifact(path, propagate_io=True)
    if kind == "missing":
        return None
    if kind != "ok":
        logger.warning("%s 读取失败，回退空配置: %s", label, err)
        return None
    if not isinstance(data, dict):
        logger.warning("%s 内容非 dict，回退空配置", label)
        return None
    return data
def _empty_fp_rules() -> dict:
    return {"rules": {}, "meta": {"updated": ""}}
def rules_of(data: dict) -> dict:
    rules = data.get("rules") if isinstance(data, dict) else None
    return rules if isinstance(rules, dict) else {}
def load_fp_rules(skill_dir: str) -> dict:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        logger.debug("load_fp_rules: skill_dir 非法(%s)，按空规则库处理", type(skill_dir).__name__)
        return _empty_fp_rules()
    path = fp_rules_path(skill_dir)
    try:
        stat = os.stat(path)
    except FileNotFoundError:
        logger.debug("load_fp_rules: 规则库尚未创建: %s", path)
        return _empty_fp_rules()
    except OSError as e:
        logger.warning("fp_rules_judge.load_fp_rules 元数据读取失败: %s", e)
        raise
    fingerprint = (stat.st_mtime_ns, stat.st_size)
    cache_key = finding_file_key(path)
    cached = _FP_RULES_CACHE.get(cache_key)
    if cached is not None and cached[0] == fingerprint:
        return copy.deepcopy(cached[1])
    data = _read_rule_store(path, "fp_rules_judge.load_fp_rules")
    if data is None:
        return _empty_fp_rules()
    if len(_FP_RULES_CACHE) >= _FP_RULES_CACHE_MAX:
        _FP_RULES_CACHE.clear()
    _FP_RULES_CACHE[cache_key] = (fingerprint, copy.deepcopy(data))
    return data
def save_fp_rules(skill_dir: str, data: dict) -> None:
    if not isinstance(data, dict):
        raise TypeError(
            f"save_fp_rules: data 必须是 dict，收到 {type(data).__name__}")
    raw_skill_dir = skill_dir
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        raise ValueError(
            "save_fp_rules: skill_dir 必须是非空路径，收到 "
            f"{type(raw_skill_dir).__name__}")
    path = fp_rules_path(skill_dir)
    payload = dict(data)
    meta = payload.get("meta")
    meta = dict(meta) if isinstance(meta, dict) else {}
    meta["updated"] = now_iso()
    payload["meta"] = meta
    cache_key = finding_file_key(path)
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        write_json_artifact(path, payload, indent=2)
    except (OSError, ValueError, TypeError, RecursionError) as e:
        logger.warning("fp_rules_judge.save_fp_rules: %s", e)
        raise
    finally:
        _FP_RULES_CACHE.pop(cache_key, None)
def _read_cv_ledger(path: str) -> Any | None:
    if not os.path.isfile(path):
        return None
    try:
        data, kind, err = read_json_artifact(path, propagate_io=True)
    except OSError as exc:
        logger.warning("[FP-Filter] 台账不可读(按缺失降级): %s: %s", path, exc)
        return None
    if kind == "ok":
        return data
    if kind != "missing":
        logger.warning("[FP-Filter] 台账不可读(按缺失降级): %s: %s", path, err)
    return None
def load_cv_fp_tracker_rates(skill_dir: str) -> dict:
    try:
        skill_dir = _path_arg(skill_dir)
        if not skill_dir:
            return {}
        data = _read_cv_ledger(fp_tracker_path(skill_dir))
        if isinstance(data, dict):
            return _shrink_fp_rates_bayesian(data)
        return {}
    except Exception as e:  # noqa: BLE001
        logger.warning("[FP-Filter] 策略15 FP率数据加载降级: %s", e)
        return {}
_BETA_PRIOR_ALPHA = 2.0
_BETA_PRIOR_BETA = 8.0
def _shrink_fp_rates_bayesian(data: dict) -> dict:
    try:
        if not isinstance(data, dict):
            return data
        _shrunk = {}
        for fam, entry in data.items():
            if not isinstance(entry, dict):
                _shrunk[fam] = entry
                continue
            total = entry.get("total", 0)
            fp = entry.get("fp", 0)
            if is_real_number(total) and is_real_number(fp) and total > 0:
                _fp_n = min(max(float(fp), 0.0), float(total))
                _total_n = float(total)
                raw_rate = _fp_n / _total_n
                shrunk_rate = (_fp_n + _BETA_PRIOR_ALPHA) / (
                    _total_n + _BETA_PRIOR_ALPHA + _BETA_PRIOR_BETA)
                _new = dict(entry)
                _new["fp_rate_raw"] = round(raw_rate, 4)
                _new["fp_rate"] = round(min(1.0, shrunk_rate), 4)
                _new["beta_pseudo_prior"] = {
                    "alpha": _BETA_PRIOR_ALPHA, "beta": _BETA_PRIOR_BETA}
                _shrunk[fam] = _new
            else:
                _shrunk[fam] = entry
        return _shrunk
    except Exception as e:  # noqa: BLE001
        logger.warning("[FP-Filter] 策略15 FP率贝叶斯收缩降级，返回原始数据: %s", e)
        return data
_INVALID_SUPPRESSION_RULE_IDS = frozenset({
    "UNKNOWN", "GENERIC", "_UNKNOWN_RULE",
})
_SUPPRESSION_PATTERN_FIELDS = ("message_patterns", "file_patterns")
def _suppression_rule_id(rule: dict) -> str:
    _raw_rid = rule.get("rule_id")
    if not isinstance(_raw_rid, str):
        logger.warning("[FP-Filter] 策略16拦截无效抑制条目(非字符串 rule_id): %r",
                       _raw_rid)
        return ""
    _rid = _raw_rid.strip()
    if not _rid or _rid.upper() in _INVALID_SUPPRESSION_RULE_IDS:
        logger.warning("[FP-Filter] 策略16拦截占位/空 rule_id 抑制条目: %r",
                       rule.get("rule_id"))
        return ""
    return _rid
def _suppression_patterns_valid(rule: dict, rid: str) -> bool:
    for field_name in _SUPPRESSION_PATTERN_FIELDS:
        patterns = rule.get(field_name, [])
        if (not isinstance(patterns, (list, tuple))
                or any(not isinstance(pattern, str) or not pattern.strip()
                       for pattern in patterns)):
            logger.warning(
                "[FP-Filter] 策略16拦截非法模式列表: rule=%s field=%s",
                rid, field_name)
            return False
    return True
def _suppression_rule_has_evidence(rule: dict, rid: str) -> bool:
    if not _suppression_patterns_valid(rule, rid):
        return False
    _has_pattern = bool(rule.get("message_patterns") or rule.get("file_patterns"))
    if not _has_pattern:
        # 空模式列表在 _patterns_hit 中返回 True（通配），等价于无差别抑制该
        # rule_id 的全部 P2/P3 发现（含真实缺陷）。fp_count 只是误报统计量，
        # 不能作为“免模式”旁路，否则抑制规则退化为全量掩盖通道。
        logger.warning(
            "[FP-Filter] 策略16拦截空模式抑制条目（空列表等价全量抑制）: "
            "rule=%s fp_count=%r", rid, rule.get("fp_count"))
        return False
    return True
SUPPRESSION_DEFAULT_MIN_SEVERITY = DEFAULT_SEVERITY
def _suppression_threshold_ok(rule: dict, rid: str) -> bool:
    _sp_min = rule.get("min_severity_to_suppress",
                       SUPPRESSION_DEFAULT_MIN_SEVERITY)
    _rank = _sev_rank_of(_sp_min)
    if _rank is None or _rank < 2:
        logger.warning(
            "[FP-Filter] 策略16拦截非法或P0/P1阈值抑制条目"
            "(未知级别失败关闭，P0/P1永不抑制): "
            "rule=%s min_severity_to_suppress=%r", rid, _sp_min)
        return False
    return True
def normalize_suppression_rule(rule) -> dict | None:
    if not isinstance(rule, dict):
        return None
    _rid = _suppression_rule_id(rule)
    if not _rid:
        return None
    if not _suppression_rule_has_evidence(rule, _rid):
        return None
    if not _suppression_threshold_ok(rule, _rid):
        return None
    rule["rule_id"] = _rid
    return rule
_FP_SUPPRESSION_OBSERVATION_TTL_DAYS = 90
_FP_SUPPRESSION_DEMOTE_DAYS = 90
_FP_SUPPRESSION_EXPIRE_DAYS = 180
_SUPPRESSION_EXPIRE_RANK = 4
def _suppression_age_days(created_at: Any) -> float | None:
    """返回抑制规则年龄（天）。无时间戳时返回 None（视为未过期）。"""
    text = as_str(created_at).strip()
    if not text:
        return None
    try:
        created = time.mktime(time.strptime(text, FMT_DATETIME))
    except (ValueError, OverflowError):
        return None
    return max(0.0, (time.time() - created) / 86400.0)
def _demote_suppression_rule(rule: dict, rank_floor: int) -> dict | None:
    """把抑制阈值抬到 rank_floor；越界说明规则已失效，返回 None。"""
    current = _sev_rank_of(rule.get(
        "min_severity_to_suppress", SUPPRESSION_DEFAULT_MIN_SEVERITY))
    if current is None:
        return None
    target = max(current, rank_floor)
    if target >= _SUPPRESSION_EXPIRE_RANK:
        return None
    if target == current:
        return rule
    demoted = dict(rule)
    demoted["demoted_from"] = rule.get("min_severity_to_suppress", "")
    demoted["min_severity_to_suppress"] = severity_literal_from_rank(target)
    return demoted
def _apply_suppression_ttl(rule: dict) -> dict | None:
    """按规则年龄做降级/失效。

    抑制规则只增不减会形成棘轮：一旦写入就永久掩盖该规则的全部低
    严重度发现，且无任何信号提示。TTL 提供时间维度的回收——观察态
    规则（小样本）过期更快，标准规则先降级再失效。

    无 `created_at` 的历史规则视为未过期（兼容旧数据），需人工清理。
    """
    age = _suppression_age_days(rule.get("created_at"))
    if age is None:
        return rule
    if rule.get("observation_mode"):
        if age >= _FP_SUPPRESSION_OBSERVATION_TTL_DAYS:
            return None
        return rule
    if age >= _FP_SUPPRESSION_EXPIRE_DAYS:
        return None
    if age >= _FP_SUPPRESSION_DEMOTE_DAYS:
        return _demote_suppression_rule(rule, 3)
    return rule
def _filter_valid_suppression_rules(raw_rules) -> list:
    valid_rules = []
    for _r in raw_rules:
        _normalized = normalize_suppression_rule(_r)
        if _normalized is None:
            continue
        _kept = _apply_suppression_ttl(_normalized)
        if _kept is None:
            logger.info(
                "[FP-Filter] 策略16抑制规则超期失效: rule=%s created_at=%r",
                _normalized.get("rule_id"),
                _normalized.get("created_at"))
            continue
        valid_rules.append(_kept)
    return valid_rules
def _suppression_rules_node(data) -> list:
    if isinstance(data, list):
        return data
    if not isinstance(data, dict):
        return []
    raw_rules = data.get("rules")
    return list(raw_rules) if isinstance(raw_rules, (list, tuple)) else []
def drop_fp_suppression_rule(skill_dir: str, rule_id: str) -> bool:
    """删除 fp_suppression.json 中该规则的抑制条目。

    撤销只复活治疗项、不动抑制规则时，下一轮同样的 finding 还会被
    同一条规则抑制，形成无法收敛的棘轮。这里在撤销成立时同步移除
    规则，保证人工/AI 判定能真正生效到下一轮。
    """
    if not rule_id:
        return False
    path = fp_suppression_path(skill_dir)
    try:
        with locked_artifact(path) as locked:
            if not locked:
                logger.warning(
                    "[FP-Filter] 抑制规则读改写锁不可用，跳过撤销: %s", path)
                return False
            data, status, _error = read_json_artifact(path)
            if status != "ok" or not isinstance(data, dict):
                return False
            rules = data.get("rules")
            if not isinstance(rules, list) or not rules:
                return False
            kept = [
                rule for rule in rules
                if not (isinstance(rule, dict)
                        and str(rule.get("rule_id", "")).strip() == rule_id)
            ]
            if len(kept) == len(rules):
                return False
            write_json_artifact(path, {"rules": kept})
            logger.info(
                "[FP-Filter] 抑制规则已撤销: rule=%s (剩余 %d 条)",
                rule_id, len(kept))
            return True
    except (OSError, ValueError, TypeError, RuntimeError) as exc:
        log_swallowed(
            __name__, exc, context='drop_fp_suppression_rule:rewrite')
        return False
def load_cv_fp_suppression_rules(skill_dir: str) -> list:
    try:
        skill_dir = _path_arg(skill_dir)
        if not skill_dir:
            return []
        return _filter_valid_suppression_rules(
            _suppression_rules_node(
                _read_cv_ledger(fp_suppression_path(skill_dir))))
    except Exception as e:  # noqa: BLE001
        logger.warning("[FP-Filter] 策略16抑制规则加载降级: %s", e)
        return []
def load_fp_tracker_rates(skill_dir: str) -> dict:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir:
        return {}
    return _read_rule_store(
        fp_tracker_rules_path(skill_dir), "fp_tracker") or {}
def load_historical_fp_rules(skill_dir: str) -> dict:
    try:
        return rules_of(load_fp_rules(skill_dir))
    except Exception as e:  # noqa: BLE001
        logger.warning("load_historical_fp_rules: 加载历史FP规则失败: %s", e)
        return {}
def get_fp_rule_ids(skill_dir: str) -> set:
    ids = {norm_rule_key(key) for key in rules_of(load_fp_rules(skill_dir))}
    ids.discard("")
    return ids
def is_fp_rule(skill_dir: str, rule_id: str) -> bool:
    key = _str_rule_key(rule_id)
    return key is not None and key in get_fp_rule_ids(skill_dir)
def fp_rule_registered(skill_dir: str, rule_id: str) -> bool:
    rule_key = _str_rule_key(rule_id)
    if rule_key is None:
        return False
    return any(is_fp_rule(skill_dir, rid)
               or _static_fp_rule_registered(rid, skill_dir)
               for rid in equiv_rule_ids(rule_key))
def _equiv_finding_column(finding: dict) -> int | None:
    for key in ("col", "column", "col_offset"):
        value = finding.get(key)
        if is_pure_int(value):
            return value
    return None
def equiv_dedup_key(finding: dict) -> tuple | None:
    data = finding if isinstance(finding, dict) else {}
    rule_id = norm_rule_key(data.get("rule_id"))
    if not rule_id:
        return None
    view = _finding_view(data)
    if (not view.file_path
            or view.file_path.strip().casefold() in _UNRESOLVED_FILE_MARKERS):
        return None
    return (finding_file_key(view.file_path), view.line,
            _equiv_finding_column(data),
            frozenset(equiv_rule_ids(rule_id)))

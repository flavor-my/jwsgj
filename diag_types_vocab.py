from __future__ import annotations

import os
import re
from dataclasses import dataclass
from enum import Enum
from typing import Any

from jwsgj.log_config import get_module_logger, log_swallowed

logger = get_module_logger(__name__)
class HallucinationType(str, Enum):
    MAPPING = "mapping"
    NAMING = "naming"
    RESOURCE = "resource"
    LOGIC = "logic"
    AI_SLOP = "ai_slop"
    TEST_ILLUSION = "test_illusion"
    MEMORY = "memory"
    SECURITY = "security"
TYPE_ALL: list[str] = [t.value for t in HallucinationType]
RULE_TYPE_MAP: dict[str, str] = {
    "H01": HallucinationType.NAMING.value,
    "H02": HallucinationType.RESOURCE.value,
    "H09": HallucinationType.RESOURCE.value,
    "H03": HallucinationType.LOGIC.value,
    "H04": HallucinationType.MAPPING.value,
    "H05": HallucinationType.AI_SLOP.value,
    "H06": HallucinationType.TEST_ILLUSION.value,
    "H07": HallucinationType.MEMORY.value,
    "H08": HallucinationType.SECURITY.value,
}
HALLUCINATION_RULE_IDS = {
    "H01": "hallucinated_api",
    "H02": "hallucinated_import",
    "H09": "hallucinated_module",
    "H03": "hallucinated_exception",
    "H04": "context_contradiction",
    "H05": "ai_slop",
    "H06": "test_illusion",
    "H07": "memory_hallucination",
    "H08": "sandbox_reflection",
}
class NormCategory(str, Enum):
    GENERATION = "G"
    VERIFICATION = "V"
    MEMORY = "M"
    COLLABORATION = "C"
    REGRESSION = "R"
class NormSeverity(str, Enum):
    P0 = "P0"
    P1 = "P1"
    P2 = "P2"
@dataclass
class NormRule:
    rule_id: str
    category: NormCategory
    severity: NormSeverity
    name: str
    description: str
    violation_consequence: str
    rationale: str
@dataclass
class NormViolation:
    rule_id: str
    category: str
    severity: str
    name: str
    description: str
    detail: str
    file_path: str = ""
    line_num: int = 0
    suggestion: str = ""
    def as_dict(self) -> dict[str, Any]:
        return {
            "rule_id": self.rule_id,
            "category": self.category,
            "name": self.name,
            "severity": self.severity,
            "description": self.description,
            "detail": self.detail,
            "file_path": self.file_path,
            "line_num": self.line_num,
            "suggestion": self.suggestion,
        }
HALLUCINATION_NORMS: list[NormRule] = [
    NormRule("G1", NormCategory.GENERATION, NormSeverity.P0,
             "禁止幻觉API",
             "每个函数调用必须确认被调函数在当前作用域或导入链中存在",
             "P0阻断",
             "幻觉API是最高频幻觉类型（17轮审计中极高频出现）"),
    NormRule("G2", NormCategory.GENERATION, NormSeverity.P0,
             "禁止except:pass吞异常",
             "异常处理必须精确捕获+日志记录或向上传播",
             "P0阻断",
             "except:pass会静默吞掉幻觉导致的NameError/ImportError，使幻觉不可见"),
    NormRule("G3", NormCategory.GENERATION, NormSeverity.P0,
             "禁止_前缀星号导入",
             "from X import *后仅可使用__all__中声明的公共成员",
             "P0阻断",
             "Python语法规定import *不导入_前缀名称，AI常忽略此规则"),
    NormRule("G4", NormCategory.GENERATION, NormSeverity.P1,
             "禁止不可执行代码",
             "每段代码必须附带验证方式（编译/导入/执行）",
             "P1严重",
             "不可执行的代码无法暴露幻觉，形成沉默的幻觉"),
    NormRule("G5", NormCategory.GENERATION, NormSeverity.P0,
             "禁止未验证声称已实现",
             "任何已完成/PASS声明必须有执行证据",
             "P0阻断",
             "幻觉记忆曾导致3257行/63PASS实际为1409行/0PASS"),
    NormRule("G6", NormCategory.GENERATION, NormSeverity.P1,
             "禁止AI Slop",
             "每段代码必须可回答删了会怎样",
             "P1严重",
             "AI Slop降低信噪比，增加维护成本"),
    NormRule("G7", NormCategory.GENERATION, NormSeverity.P0,
             "禁止沙箱反射链",
             "exec沙箱禁止globals/locals/vars/dir/setattr/getattr",
             "P0阻断",
             "getattr+__subclasses__链可绕过__import__移除实现逃逸"),
    NormRule("V1", NormCategory.VERIFICATION, NormSeverity.P0,
             "compile不用ast.parse",
             "语法验证必须使用compile(src, name, 'exec')",
             "P0阻断",
             "ast.parse不检查__future__位置，导致88个文件语法错误被漏检"),
    NormRule("V2", NormCategory.VERIFICATION, NormSeverity.P0,
             "验证前清除pyc缓存",
             "任何导入链验证前必须清除__pycache__",
             "P0阻断",
             "pyc缓存掩盖导入链断裂，使ImportError不可见"),
    NormRule("V3", NormCategory.VERIFICATION, NormSeverity.P1,
             "验证覆盖调用方",
             "不仅检查定义方，也检查调用方是否引用了定义",
             "P1严重",
             "函数定义≠功能接入，__all__和语法正确不等于被调用"),
    NormRule("V4", NormCategory.VERIFICATION, NormSeverity.P0,
             "逐文件验证",
             "每个文件修改后独立验证再继续下一个",
             "P0阻断",
             "批量修复导致文件大面积损坏且难以定位（D5规则）"),
    NormRule("V5", NormCategory.VERIFICATION, NormSeverity.P0,
             "修改前备份",
             "任何文件修改前必须备份到 <会话工作空间>/Temp/_backups/（get_backup_base 归口，禁止技能根及其他任何非工作空间位置）",
             "P0阻断",
             "确保可回滚（D8规则）"),
    NormRule("V6", NormCategory.VERIFICATION, NormSeverity.P0,
             "删除前验证功能迁移",
             "死代码删除前确认业务功能在其他地方实现",
             "P0阻断",
             "防止删除看似无用实则有用的代码（D6规则）"),
    NormRule("M1", NormCategory.MEMORY, NormSeverity.P0,
             "记录已实现前AST验证",
             "写入已完成/XX PASS前必须执行ast.walk确认函数存在",
             "P0阻断",
             "记忆本身也会幻觉，曾记录不存在的3257行/63PASS"),
    NormRule("M2", NormCategory.MEMORY, NormSeverity.P1,
             "区分计划态与完成态",
             "计划态用TODO/计划标记，完成态含可量化验证指标",
             "P1严重",
             "混淆计划与完成会导致后续会话基于错误记忆工作"),
    NormRule("M3", NormCategory.MEMORY, NormSeverity.P1,
             "summary含校验锚点",
             "记忆摘要中的行数/函数数/PASS数必须可被后续快速校验",
             "P1严重",
             "提供可验证的量化指标，而非不可核验的定性描述"),
    NormRule("M4", NormCategory.MEMORY, NormSeverity.P0,
             "矛盾时必须更正",
             "发现记忆与代码实际状态不符时立即修正记忆",
             "P0阻断",
             "错误记忆会持续误导后续会话"),
    NormRule("C1", NormCategory.COLLABORATION, NormSeverity.P0,
             "人类必须审查AI代码",
             "AI生成的代码必须经人类审查后方可合入",
             "P0阻断",
             "AI无法100%自我验证，人类审查是最后一道防线"),
    NormRule("C2", NormCategory.COLLABORATION, NormSeverity.P0,
             "关键路径人工确认",
             "安全相关/数据操作/不可逆操作需人类确认",
             "P0阻断",
             "幻觉代码在关键路径上可能造成不可恢复的损失"),
    NormRule("C3", NormCategory.COLLABORATION, NormSeverity.P1,
             "AI声明不确定性",
             "AI对生成的每段代码标注置信度（高/中/低）",
             "P1严重",
             "让人类知道哪些代码需要重点审查"),
    NormRule("C4", NormCategory.COLLABORATION, NormSeverity.P1,
             "负面约束优先",
             "先告诉AI不要做什么再告诉要做什么",
             "P1严重",
             "负面约束比正面指令更有效防止幻觉"),
    NormRule("R1", NormCategory.REGRESSION, NormSeverity.P0,
             "修改后对比基线",
             "修改后重新运行诊断工具与STEP0基线对比",
             "P0阻断",
             "确认修改未引入新问题（CodeOps STEP3）"),
    NormRule("R2", NormCategory.REGRESSION, NormSeverity.P0,
             "失败自动回滚",
             "验证失败时自动从备份恢复",
             "P0阻断",
             "防止幻觉修复引入新的幻觉"),
    NormRule("R3", NormCategory.REGRESSION, NormSeverity.P0,
             "3次违规阻断会话",
             "同一会话内累计3次规则违规触发阻断",
             "P0阻断",
             "防止小错不断累积成大问题"),
]
NORM_INDEX: dict[str, NormRule] = {n.rule_id: n for n in HALLUCINATION_NORMS}
SANDBOX_REFLECTION_FUNCS: frozenset[str] = frozenset({
    "globals", "locals", "vars", "dir", "setattr", "getattr"})
_CLAIM_NUMBER = r'((?:\d{1,3}(?:,\d{3})+|\d+))'
_CLAIM_NUMBER_LEFT = r'(?<![\d.,/+A-Za-z_-])'
LINE_CLAIM_RE = re.compile(
    rf'{_CLAIM_NUMBER_LEFT}{_CLAIM_NUMBER}\s*(?:行|lines?\b|LOC\b)',
    re.IGNORECASE)
FUNC_CLAIM_RE = re.compile(
    rf'{_CLAIM_NUMBER_LEFT}{_CLAIM_NUMBER}\s*(?:个)?'
    r'(?:函数|functions?\b|funcs?\b)',
    re.IGNORECASE)
PASS_CLAIM_RE = re.compile(
    rf'{_CLAIM_NUMBER_LEFT}{_CLAIM_NUMBER}\s*'
    r'(?:PASS(?:ED)?\b|tests?\s+passed\b|passed\s+tests?\b)',
    re.IGNORECASE)
PASS_SUFFIX_CLAIM_RE = re.compile(
    rf'(?<![_\dA-Za-z])PASS(?:ED)?\s*{_CLAIM_NUMBER}(?![\d.,%/_+A-Za-z-])',
    re.IGNORECASE)
ORDINAL_LINE_RE = re.compile(rf'第\s*{_CLAIM_NUMBER}\s*行')
ORDINAL_FUNC_RE = re.compile(rf'第\s*{_CLAIM_NUMBER}\s*(?:个)?函数')
ORDINAL_PASS_RE = re.compile(
    rf'第\s*{_CLAIM_NUMBER}\s*(?:个)?PASS', re.IGNORECASE)
THRESHOLD_PREFIX_OPS = "><=≥≤~≈+"
THRESHOLD_PREFIX_WORDS = (
    "超过", "超出", "多于", "少于", "不足", "至多", "至少",
    "最多", "最少", "大于", "小于", "超", "逾", "下方", "上方",
    "more than", "less than", "greater than", "fewer than", "at least",
    "at most", "no more than", "no less than", "up to", "over", "under",
    "above", "below", "exceeding", "max", "min", "maximum", "minimum",
)
THRESHOLD_SUFFIX_WORDS = (
    "以上", "以下", "以内", "开外", "窗口",
    "or more", "or less", "or fewer", "or above", "or below",
    "plus", "max", "min",
)
_THRESHOLD_PREFIX_FOLDED = tuple(w.casefold() for w in THRESHOLD_PREFIX_WORDS)
_THRESHOLD_SUFFIX_FOLDED = tuple(w.casefold() for w in THRESHOLD_SUFFIX_WORDS)
def is_threshold_context(claim: str, match: re.Match[str]) -> bool:
    start = match.start(1)
    i = start - 1
    while i >= 0 and claim[i].isspace():
        i -= 1
    if i >= 0:
        if claim[i] in THRESHOLD_PREFIX_OPS:
            return True
        head = claim[max(0, i - 40):i + 1].casefold()
        for word in _THRESHOLD_PREFIX_FOLDED:
            if not head.endswith(word):
                continue
            boundary = len(head) - len(word) - 1
            if boundary < 0:
                return True
            previous = head[boundary]
            if (word.isascii() and previous.isascii()
                    and (previous.isalnum() or previous == '_')):
                continue
            return True
    tail = claim[match.end():].lstrip().casefold()
    if tail.startswith(("+", "%", "/")):
        return True
    return tail.startswith(_THRESHOLD_SUFFIX_FOLDED)
def claim_number(match: re.Match[str]) -> int:
    return int(match.group(1).replace(",", ""))
def first_quantity_claim(claim: str, claim_re: re.Pattern[str],
                         ordinal_re: re.Pattern[str]) -> re.Match[str] | None:
    ordinal_starts = {m.start(1) for m in ordinal_re.finditer(claim)}
    for match in claim_re.finditer(claim):
        if match.start(1) in ordinal_starts:
            continue
        if is_threshold_context(claim, match):
            continue
        return match
    return None
class SizeGateStatus(Enum):
    PASS = "PASS"
    WARN = "WARN"
    BLOCK = "BLOCK"
class FileRole(str, Enum):
    CORE = "core"
    DETECTOR = "detector"
    REGISTRY = "registry"
    TEST = "test"
    PIPELINE = "pipeline"
    DEFAULT = "default"
ROLE_PATTERNS: dict[FileRole, tuple[list[str], int]] = {
    FileRole.CORE: ([r"(?:^|/)core/", r"(?:^|/)core(?=[/_.-]|$)",
                     r"engine", r"autofix", r"main_engine"], 1),
    FileRole.DETECTOR: ([r"detector", r"(?:^|/)checks/", r"scanner", r"rule"], 1),
    FileRole.REGISTRY: ([r"registry", r"register"], 1),
    FileRole.TEST: ([r"(^|/)test_[^/]*\.py$", r"(^|/)[^/]*_test\.py$",
                     r"(^|/)tests?/"], 1),
    FileRole.PIPELINE: ([r"(?:^|/)pipeline/",
                         r"(?:^|/)pipeline(?=[/_.-]|$)"], 1),
    FileRole.DEFAULT: ([], 0),
}
_ROLE_RE_CACHE: dict[str, re.Pattern[str]] = {
    pattern: re.compile(pattern)
    for _patterns, _ in ROLE_PATTERNS.values()
    for pattern in _patterns
}
def _role_pattern_re(pattern: str) -> re.Pattern[str]:
    compiled = _ROLE_RE_CACHE.get(pattern)
    if compiled is None:
        compiled = re.compile(pattern)
        _ROLE_RE_CACHE[pattern] = compiled
    return compiled
def coerce_task_type(task_type: Any, default: str) -> str:
    if not isinstance(task_type, str):
        return default
    return task_type.strip().lower() or default
def normalize_filepath(file_path: Any) -> str:
    if isinstance(file_path, str):
        return file_path
    if isinstance(file_path, (bytes, bytearray)):
        return os.fsdecode(bytes(file_path))
    if isinstance(file_path, os.PathLike):
        try:
            return os.fsdecode(file_path)
        except (TypeError, ValueError, OSError) as _e:
            log_swallowed(__name__, _e,
                          context=f'normalize_filepath:{type(_e).__name__}')
            return ""
    return ""
def classify_file_role(file_path: str) -> FileRole:
    file_path = normalize_filepath(file_path)
    if not file_path:
        return FileRole.DEFAULT
    path_lower = file_path.lower().replace("\\", "/")
    best_role = FileRole.DEFAULT
    best_score = 0
    for role, (patterns, threshold) in ROLE_PATTERNS.items():
        score = sum(1 for p in patterns if _role_pattern_re(p).search(path_lower))
        if role is FileRole.TEST and score >= threshold:
            return FileRole.TEST
        if score >= threshold and score > best_score:
            best_score = score
            best_role = role
    return best_role
_ROLE_FILE_BUDGET_LINES = 3000
_ROLE_FUNC_BUDGET_LINES = 300
_ROLE_CLASS_BUDGET_LINES = 400
ROLE_HARD_THRESHOLDS: dict[FileRole, tuple[int, int, int]] = {
    FileRole.CORE:     (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES,
                        _ROLE_CLASS_BUDGET_LINES),
    FileRole.DETECTOR: (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES,
                        _ROLE_CLASS_BUDGET_LINES),
    FileRole.REGISTRY: (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES, 300),
    FileRole.TEST:     (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES,
                        _ROLE_CLASS_BUDGET_LINES),
    FileRole.PIPELINE: (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES,
                        _ROLE_CLASS_BUDGET_LINES),
    FileRole.DEFAULT:  (_ROLE_FILE_BUDGET_LINES, _ROLE_FUNC_BUDGET_LINES,
                        _ROLE_CLASS_BUDGET_LINES),
}
def get_role_thresholds(role: FileRole) -> tuple[int, int, int]:
    if isinstance(role, FileRole):
        return ROLE_HARD_THRESHOLDS.get(
            role, ROLE_HARD_THRESHOLDS[FileRole.DEFAULT])
    try:
        normalized = FileRole(str(role).strip().lower())
    except (TypeError, ValueError):
        return ROLE_HARD_THRESHOLDS[FileRole.DEFAULT]
    return ROLE_HARD_THRESHOLDS.get(
        normalized, ROLE_HARD_THRESHOLDS[FileRole.DEFAULT])
_BASE_BUDGET_FILE_LINES = _ROLE_FILE_BUDGET_LINES
_BASE_BUDGET_FUNC_LINES = _ROLE_FUNC_BUDGET_LINES
TASK_BUDGET_FACTOR: dict[str, float] = {
    "code_write": 1.0,
    "refactor": 0.8,
    "fix": 0.9,
    "create": 1.0,
    "test_write": 1.0,
    "doc_write": 2000 / 3000,
    "general": 1.0,
}
_TASK_BUDGET_ADVICE: dict[str, str] = {
    "code_write": "代码生成任务,单文件≤{max_file}行",
    "refactor": "重构任务,按基准{pct}%收紧预算",
    "fix": "修复任务,按基准{pct}%收紧预算",
    "create": "从零创建任务,与代码生成同预算",
    "test_write": "测试编写,遵循测试规范",
    "doc_write": "文档任务,简洁优先",
    "general": "通用任务预算",
}
TASK_BUDGETS: dict[str, dict[str, Any]] = {
    task: {
        "max_file": round(_BASE_BUDGET_FILE_LINES * factor),
        "max_func": round(_BASE_BUDGET_FUNC_LINES * factor),
        "advice": _TASK_BUDGET_ADVICE[task].format(
            max_file=round(_BASE_BUDGET_FILE_LINES * factor),
            pct=round(factor * 100)),
    }
    for task, factor in TASK_BUDGET_FACTOR.items()
}
NEAR_BUDGET_RATIO = 0.8
DEFAULT_SESSION_QUOTA: dict[str, int] = {
    "max_total_lines": 50000,
}
DEFAULT_TASK_TYPE = "code_write"
PROJECT_ROOT_MARKERS: tuple[str, ...] = (
    "SKILL.md", ".git", "pyproject.toml", "setup.py", "setup.cfg",
    "Pipfile", "poetry.lock", "tox.ini", "requirements.txt",
)
MSG_SYNTAX_ERROR_SKIP = "SyntaxError parsing source, skipping"
MSG_SYNTAX_ERROR_SKIP_DETECTION = "SyntaxError parsing source, skipping detection"
MSG_EXCEPTION_BROAD_HANDLER = "Exception caught in broad handler"
MSG_OSERROR_CONTINUE = "[OSError] 操作失败但继续执行"
MSG_OSERROR_SUPPRESSED = "jwsgj: suppressed OSError"
MSG_OSERROR_DEGRADED = "degraded: OSError"
MSG_XV_VALIDATORS_IMPORT_FAIL = "[XV-Validators] 导入/执行失败: %s"
MSG_CONFIRM_SKILL_DIR = "确认技能目录可访问，重新运行诊断"
RULE_HIGH_COMPLEXITY = "high_complexity"
RULE_HARDCODED_CREDENTIAL = "hardcoded_credential"  # jwsgj:suppress SE-03 E1-HARDCODED-CRED — 规则 ID 字符串常量，非凭据
RULE_UNREACHABLE_CODE = "unreachable_code"
RULE_COMMAND_INJECTION = "command_injection"
RULE_ORPHAN_FUNCTION = "orphan_function"
RULE_BROAD_EXCEPTION = "broad_exception"
RULE_MISSING_ANNOTATIONS = "missing_annotations"
RULE_MISSING_DOCSTRING = "missing_docstring"
RULE_TOO_MANY_PARAMS = "too_many_params"
RULE_HARDCODED_SECRET = "hardcoded_secret"  # jwsgj:suppress SE-03 E1-hardcoded_secret hardcoded_secret — 规则 ID 字符串常量，非凭据
RULE_MUTABLE_DEFAULT = "mutable_default"
RULE_CONNECTION_LEAK = "connection_leak"
RULE_INSECURE_CONFIG = "insecure_config"
RULE_PUBLIC_UNTESTED = "public_untested"
UNTESTED_COVERAGE_BLINDSPOT_TYPES = frozenset({
    "no_test_coverage", "undertested", RULE_PUBLIC_UNTESTED,
})
FUNCTION_ORPHAN_BLINDSPOT_TYPES = frozenset({
    RULE_ORPHAN_FUNCTION, RULE_PUBLIC_UNTESTED, "orphan", "untested_public",
})
D_ARCH_RULE_SUGGESTIONS: dict[str, str] = {  # jwsgj:suppress E1-MUTABLE-GLOBAL TP-07 — 审计认可：规则建议表，仅模块导入期做一次别名赋值，非共享状态缺陷
    'D08': '移除自引用导入，重构代码结构',
    'D09': '合并须附 pros/cons/net_benefit=positive 论证并留痕（GOV-02）',
    'D14': '收敛公共面：合并职责重复的导出、把仅内部使用的符号私有化；禁止拆分子门面模块（GOV-01）',
    'D27': '移除未使用的导入',
}
D_ARCH_RULE_SUGGESTIONS['D12'] = D_ARCH_RULE_SUGGESTIONS['D09']
@dataclass
class CodeRegion:
    file: str
    start_line: int
    end_line: int
    node_type: str = ""
    node_name: str = ""
DIAG_REPORT_DIRNAME = "zhenduan"
CAT_MAINTAINABILITY = "maintainability"
SPLIT_SAFETY_DIMENSION = "split-safety"
CAT_EXCEPTION_HANDLING = "exception_handling"
CAT_DISCOVERABILITY = "discoverability"
CAT_CROSS_VALIDATION = "cross_validation"
CAT_DYNAMIC_BINDING = "dynamic_binding"
CAT_DYNAMIC_IMPORTS = "dynamic_imports"
CAT_DYNAMIC_DISPATCH = "dynamic_dispatch"
RULE_ID_PREFIX_CATEGORY: dict[str, str] = {
    'SYN': 'syntax_error', 'SY': 'syntax_error',
    'IN': 'unused_import', 'IMP': 'unused_import',
    'SE': 'security', 'SEC': 'security', 'SC': 'security', 'SR': 'security',
    'NW': 'security',
    'D9': 'architecture',
    'DC': 'dead_code',
    'BE': 'exception_handling', 'EX': 'exception_handling',
    'CQ': 'complexity', 'CX': 'complexity',
    'RES': 'resource', 'RL': 'resource',
    'CF': 'config',
    'API': 'api_compat',
    'TS': 'testing', 'TC': 'testing',
    'ARCH': 'architecture',
}
TAINT_SOURCE_CATEGORY_BY_NAME: dict[str, str] = {
    "os.environ": "environment",
    "os.environ.get": "environment",
    "os.getenv": "environment",
    "sys.argv": "user_input",
    "sys.stdin": "user_input",
    "input": "user_input",
    "raw_input": "user_input",
    "request.GET": "user_input",
    "request.POST": "user_input",
    "request.body": "user_input",
    "request.COOKIES": "user_input",
    "request.META": "user_input",
    "request.args": "user_input",
    "request.form": "user_input",
    "request.files": "user_input",
    "request.values": "user_input",
    "request.json": "user_input",
    "request.data": "user_input",
    "request.cookies": "user_input",
    "request.headers": "user_input",
    "flask.request.args": "user_input",
    "flask.request.form": "user_input",
    "flask.request.files": "user_input",
    "flask.request.json": "user_input",
    "flask.request.values": "user_input",
    "flask.request.data": "user_input",
    "flask.request.cookies": "user_input",
    "flask.request.headers": "user_input",
    "flask.request.args.get": "user_input",
    "flask.request.form.get": "user_input",
    "flask.request.files.get": "user_input",
    "flask.request.json.get": "user_input",
    "flask.request.values.get": "user_input",
    "flask.request.data.get": "user_input",
    "flask.request.cookies.get": "user_input",
    "flask.request.headers.get": "user_input",
}
TAINT_LOCAL_TRUSTED_CATEGORIES: frozenset[str] = frozenset({
    "environment", "file_input",
})
ROOT_SUBSYSTEM = "root"
FIELD_POTENTIAL_FP = "potential_false_positive"
FIELD_FALSE_NEGATIVE_RISK = "false_negative_risk"
FIELD_RECOMMENDATIONS = "recommendations"
FIELD_TOTAL_FUNCTIONS = "total_functions"
FIELD_ADJUSTED_CONFIDENCE = "adjusted_confidence"
FIELD_SUGGESTED_VALUE = "suggested_value"
FIELD_TOTAL_BLINDSPOTS = "total_blindspots"
FIELD_OPTIMIZED_DESCRIPTION = "optimized_description"
FIELD_TRIGGER_EXAMPLES = "trigger_examples"
MANDATORY_PIPELINE_TRIGGER_KEYWORDS: tuple[str, ...] = (
    "bug", "缺陷", "扇出", "测试", "诊断", "治疗", "验证",
    "审计", "分析", "检查", "优化", "死代码", "清理",
)
FIELD_CAPABILITY_COVERAGE = "capability_coverage"
FIELD_DISCOVERABILITY_INDEX = "discoverability_index"
FIELD_OPTIMIZED_KEYWORDS = "optimized_keywords"
FIELD_SYNONYM_COVERAGE = "synonym_coverage"
FIELD_TOTAL_INPUT_FINDINGS = "total_input_findings"
FIELD_METHODS_EXECUTED = "methods_executed"
FIELD_FINDINGS_SUPPRESSED = "findings_suppressed"
FIELD_EVIDENCE_STRENGTH = "evidence_strength"
FIELD_BASE_CONFIDENCE = "base_confidence"
FIELD_SIDE_EFFECTS_DETECTED = "side_effects_detected"
FIELD_EXPECTED_IMPACT = "expected_impact"
FIELD_RULES_TRIGGERED = "rules_triggered"
FIELD_INTERMEDIATE_REPORTS = "intermediate_reports"
FIELD_REGRESSION_FAILED = "regression_failed"
FIELD_SAFETY_VERIFIER_USED = "safety_verifier_used"
FIELD_ROUTED_TO_FIXER = "routed_to_fixer"
FIELD_METHOD_THRESHOLDS = "method_thresholds"
FIELD_CV_CONFIDENCE_THRESHOLDS = "cv_confidence_thresholds"
FIELD_METHOD_CONFIDENCE_MULTIPLIERS = "method_confidence_multipliers"
FIELD_THRESHOLD_ADJUST = "threshold_adjust"
FIELD_CV_RULE_WEIGHTS = "cv_rule_weights"
FIELD_EVIDENCE_FAMILIES = "evidence_families"
FIELD_EXECUTION_ERROR = "execution_error"
FIELD_SIDE_EFFECT_SUMMARY = "side_effect_summary"
FIELD_FROZEN_ROUNDS_REMAINING = "frozen_rounds_remaining"
FIELD_CODE_LEVEL_FEEDBACK = "code_level_feedback"
FIELD_ROLLBACK_RECOMMENDED = "rollback_recommended"
FIELD_DIAGNOSIS_METHOD = "diagnosis_method"
FIELD_MUTATION_CONFIRMED = "mutation_confirmed"
SIGNAL_MUTATION_CONFIRMED_DEAD = "_mutation_is_confirmed_dead"
SIGNAL_MUTATION_VERIFIED = "_mutation_verified"
METHOD_SUB_RULES: dict[str, dict[str, dict]] = {
    "B": {
        "PY01": {"weight": 0.95, "fp_rate": 0.05},
        "PY02": {"weight": 0.85, "fp_rate": 0.12},
        "PY03": {"weight": 0.70, "fp_rate": 0.25},
        "PY04": {"weight": 0.55, "fp_rate": 0.40},
        "PY05": {"weight": 0.80, "fp_rate": 0.15},
        "PY06": {"weight": 0.90, "fp_rate": 0.08},
        "SE-06": {"weight": 0.88, "fp_rate": 0.09},
        "SE-20": {"weight": 0.82, "fp_rate": 0.14},
        "DC-01": {"weight": 0.78, "fp_rate": 0.18},
        "GF-07": {"weight": 0.68, "fp_rate": 0.28},
        "D36": {"weight": 0.90, "fp_rate": 0.07},
        "D37": {"weight": 0.65, "fp_rate": 0.30},
        "D22": {"weight": 0.62, "fp_rate": 0.34},
        "CH01-HARD-CYCLE": {"weight": 0.90, "fp_rate": 0.08},
    },
}
CONF_FLOOR: float = 0.30
CONF_LOW: float = 0.40
CONF_MEDIUM: float = 0.60
CONF_HIGH: float = 0.70
CONF_VERY_HIGH: float = 0.85
CONF_CAP: float = 0.95
LOW_RELIABILITY_BASE: float = 0.90
FP_RATE_VERY_LOW: float = 0.10
FP_RATE_LOW: float = 0.15
FP_RATE_MEDIUM: float = 0.20
FP_RATE_HIGH: float = 0.25
FP_RATE_CRITICAL: float = 0.30
CONF_BOOST_SMALL: float = 0.05
CONF_BOOST_STEP: float = 0.10
CONF_BOOST_MODERATE: float = 0.15
CONF_PENALTY_MODERATE: float = 0.20
CONF_DEFAULT_PENALTY: float = 0.80
AUTO_THRESHOLD_DECAY: float = 0.85
SIGNAL_BASELINE_PERSISTENT_NOISE = "_baseline_is_persistent_noise"
SIGNAL_REFDEPTH_ISOLATED = "_refdepth_is_isolated"
SIGNAL_ENSEMBLE_LOW_CONFIDENCE = "_ensemble_is_low_confidence"
SIGNAL_REFDEPTH_PRIORITY_BOOST = "_refdepth_priority_boost"
SIGNAL_REFDEPTH_IN_DEGREE = "_refdepth_in_degree"
SIGNAL_REFDEPTH_CHAIN_DEPTH = "_refdepth_chain_depth"
SIGNAL_BASELINE_HIT_COUNT = "_baseline_hit_count"
SIGNAL_ENSEMBLE_GROUP_COUNT = "_ensemble_group_count"
SIGNAL_PARTIAL_SOURCES = "_partial_sources"
SIGNAL_BIZFLOW_CONFIDENCE_BOOST = "_bizflow_confidence_boost"
SIGNAL_REFDEPTH_CONFIDENCE_BOOST = "_refdepth_confidence_boost"
SIGNAL_DEGRADE_FACTOR = "_degrade_factor"
SIGNAL_STAGE1_FP_CANDIDATE = "_stage1_fp_candidate"
SIGNAL_STATS_DRIVEN_CANDIDATE = "_fp_stats_driven_candidate"
FIELD_QUALITY_REASONS = "quality_reasons"
TX_FIXED_STATUSES = ("fixed", "succeeded", "ai_fixed")
TX_FAILED_STATUSES = ("failed", "error")
TX_ROLLED_BACK_STATUSES = ("rolled_back",)
TX_FP_CONFIRMED_STATUSES = ("fp_confirmed",)
NO_CODE_SCORE: float = 100.0
NO_CODE_DETAIL = "无代码面（不适用）"
SUMMARY_STATUS_BUCKETS: dict[str, tuple[str, ...]] = {
    "auto_fixed": TX_FIXED_STATUSES,
    "fix_rolled_back": TX_ROLLED_BACK_STATUSES,
    "fix_failed": TX_FAILED_STATUSES,
    "needs_review": ("suggestion",),
    "no_fixer": ("no_fixer",),
    "file_not_found": ("file_not_found",),
    "fp_confirmed": TX_FP_CONFIRMED_STATUSES,
}
FMT_DATETIME = "%Y-%m-%d %H:%M:%S"
FMT_DATETIME_ISO = "%Y-%m-%dT%H:%M:%S"
MD_TABLE_SEP_3COL = "|------|------|------|"
SUBPROCESS_CHECK_CALL = "subprocess.check_call"
SUBPROCESS_CHECK_OUTPUT = "subprocess.check_output"
MULTIPROCESSING_MODULE = "multiprocessing"
CODING_UTF8 = "# -*- coding: utf-8 -*-"
SENSITIVE_NAME_KEYWORDS = ("password", "passwd", "secret", "api_key",
                           "apikey", "token", "access_key", "private_key")
YAML_SAFE_LOADERS: frozenset[str] = frozenset({
    "SafeLoader", "CSafeLoader", "BaseLoader", "CBaseLoader",
})
INPLACE_MUTATING_METHODS: frozenset[str] = frozenset({
    "add", "append", "clear", "difference_update", "discard", "extend",
    "insert", "intersection_update", "pop", "popitem", "remove",
    "reverse", "setdefault", "sort", "symmetric_difference_update",
    "update", "__delitem__", "__iadd__", "__iand__", "__imul__",
    "__ior__", "__isub__", "__ixor__", "__setitem__",
})
class GateDecision(Enum):
    PASS = "PASS"
    WARN = "WARN"
    BLOCK = "BLOCK"
class Severity(Enum):
    CRITICAL = "CRITICAL"
    HIGH = "HIGH"
    MEDIUM = "MEDIUM"
    LOW = "LOW"
    INFO = "INFO"
class SplitStrategy(Enum):
    BY_RESPONSIBILITY = "by_responsibility"
    BY_COHESION = "by_cohesion"
    BY_DEPENDENCY = "by_dependency"
    BY_LAYER = "by_layer"
    STRANGLER_FIG = "strangler_fig"
    EXTRACT_TILL_DROP = "extract_till_drop"
    HYBRID = "hybrid"
    NONE = "none"
class Thresholds:
    FUNC_LINES_BLOCK = 50
    FUNC_LINES_RECOMMEND = 30
    PARAMS_BLOCK = 5
    PARAMS_RECOMMEND = 3
    CYCLOMATIC_BLOCK = 20
    CYCLOMATIC_RECOMMEND = 10
    COGNITIVE_BLOCK = 30
    COGNITIVE_RECOMMEND = 15
    NESTING_BLOCK = 5
class EntryDecision(Enum):
    ALLOW = "allow"
    BLOCK = "block"
    SPLIT_REQUIRED = "split_required"
    WARN = "warn"
FINDING_KEY_ALIASES: dict[str, tuple[str, ...]] = {
    "file": ("file", "path", "file_path", "filepath", "location"),
    "rule_id": ("rule_id", "id", "rule", "detector_id", "rule_ref"),
    "message": ("message", "description", "title"),
    "line": ("line", "lineno", "line_no", "line_number"),
    "severity": ("severity",),
    "suggestion": ("suggestion", "fix_guidance"),
}
FINDING_KEY_SPEC: dict[str, str] = {
    "rule_id": "命中规则/检测器标识（跨轮稳定关联键、误报固化/修复经验与"
               " CV 证据网的主连接键；别名 id/rule/detector_id/rule_ref 经"
               " normalize_finding 归一出口 rule_id）",
    "severity": "严重度词系（P0/P1/P2/P3 为主流；安全域兼容 CRITICAL/HIGH"
                "与 ERROR/WARN/INFO——消费方按所在域词表解释，归一不改值）",
    "file": "目标文件路径 canonical 键（构造点主流形态；别名 path/file_path/"
            "filepath/location 归一出口 file；Finding.location、PatternFinding."
            "filepath 等 dataclass 经 to_dict() 后等价适用）",
    "line": "目标行号（非负 int，0/缺失=文件级或无行级定位；别名 lineno/line_no/"
            "line_number 与 diag_detector_findings._LINE_ALIASES 同源，仅在 line "
            "缺失或非真值时补位，不含 start_line/begin_line（区域起点属 span 口径）；"
            "归一侧严格 int 收口，bool/负数/浮点/数值文本均归 0，与留痕侧 "
            "xv_findings_core._norm_line_identity（_coerce_line 宽松直通，保留负数/"
            "浮点并接受数值文本）口径不同，跨侧对齐须在入口显式归一）",
    "message": "问题描述主文本（别名 description/title 归一出口 message；"
               "如三键并存以 message 优先，其余保留原键不吞没）",
    "suggestion": "修复建议文本（别名 fix_guidance 归一出口 suggestion）",
    "confidence": "生产端置信度（可选；None=未评估语义，归一侧不臆造默认）",
    "metrics": "检测指标容器（dict；Finding dataclass 契约字段，可选透传）",
    "references": "证据引用清单（list[str]；Finding dataclass 契约字段，可选）",
    "type": "检测类型/家族标签（可选；xv 域归类辅助，不归一不裁减）",
    "source": "来源引擎/方法标识（可选；跨引擎证据对齐辅助，不归一）",
}
def describe_finding_keys() -> dict:
    return {
        "canonical_keys": dict(FINDING_KEY_SPEC),
        "aliases": {k: tuple(v) for k, v in FINDING_KEY_ALIASES.items()},
        "normalizer": "normalize_finding(finding) — 读侧归一（补齐非替代，"
                      "line 恒非负 int）",
    }
STAGE_METRICS_KEY_SPEC: dict[str, dict[str, str]] = {
    "diagnosis_done": {
        "diag_completed": "已完成诊断方法数",
        "diag_total": "诊断方法总数",
        "source_hash": "本次诊断绑定源码指纹（复用判定锚）",
        "diagnosis_round_ts": "诊断轮次时间戳",
        "diagnosis_reused": "本次是否复用历史诊断结果（True=复用）",
        "reuse_reason": "复用原因（源码未变更等）",
    },
    "cv_regression_done": {
        "regression_has_changes": "回归上下文是否存在变更文件",
        "regression_changed_files": "变更文件数",
    },
    "cv_main_done": {
        "cv_total_findings": "CV 后 findings 总数",
        "cv_suppressed": "CV 抑制（误报过滤）数",
        "cv_rules_triggered": "命中 CV 规则数",
    },
    "fanout_done": {
        "fanout_summary": "扇出族/位点/新增位点统计",
        "fanout_html_path": "扇出报告 HTML 落盘路径",
    },
    "plan_dry_done": {
        "dry_route_confirmed": "dry 路由确认的治疗项数",
    },
    "plan_generated": {
        "plan_total_items": "治疗方案治疗项总数",
        "plan_auto_safe": "auto_safe 治疗项数",
    },
    "treatment_done": {
        "treat_total": "治疗项总数",
        "treat_executed": "已执行治疗项数",
        "treat_succeeded": "修复成功治疗项数",
        "treat_failed": "执行失败治疗项数",
        "treat_rolled_back": "回滚治疗项数",
        "treat_skipped": "跳过治疗项数",
        "treat_fp_confirmed": "误报确认治疗项数",
        "treat_pending_confirm": "待确认治疗项数",
        "treat_suggestion": "仅建议终态治疗项数",
        "treat_no_fixer": "无修复器治疗项数",
        "treat_ai_fixed": "AI 修复完成治疗项数",
        "treat_status": "治疗状态快照（completed/no_plan 等，≤200 字符截断）",
    },
    "ai_fix_pending": {
        "pending_ai_review": "待 AI 审核条目数（阶段4b 改道相位）",
    },
    "ai_fix_done": {
        "ai_fix_total": "AI 修复候选总数（仅阶段4a 候选执行路径写入）",
        "ai_fix_applied": "已应用修复数（仅阶段4a 候选执行路径写入）",
        "ai_fix_rejected": "拒绝修复数（仅阶段4a 候选执行路径写入）",
        "ai_fix_failed": "修复失败数（仅阶段4a 候选执行路径写入）",
        "zero_leftover_passed": "零遗留门禁通过（仅阶段4a 候选执行路径写入；阶段4b 审核清零放行时刻零遗留门禁尚未复核，不臆造）",
        "pending_ai_review": "审核清零放行时刻待审数（仅阶段4b 清零路径写入，恒 0；两路径各写可确定事实，不臆造另一路径数据）",
    },
    "review_done": {
        "review_score": "复盘总评分",
        "review_grade": "复盘等级",
    },
    "fupan_done": {
        "fupan_quality_score": "阶段6a fupan 质量评分",
        "fupan_memory_ops": "记忆操作数（推进点已计数化）",
        "fupan_risks": "检出风险数（推进点已计数化）",
    },
    "feedback_done": {
        "feedback_diag_count": "诊断反馈条数（容器计数化）",
        "feedback_cv_count": "CV 反馈条数（容器计数化）",
        "feedback_fixer_count": "修复器反馈条数（容器计数化）",
    },
    "code_feedback_done": {
        "completed_at": "阶段6c 完成时刻（人类可读）",
        "code_feedback_l1": "L1 级代码反哺应用数",
        "code_feedback_l2": "L2 级代码反哺应用数",
        "code_feedback_l3": "L3 级代码反哺应用数",
    },
    "evolution_pending": {
        "pending_ai_review": "待 AI 审核反哺条目数（阶段6e 改道相位）",
    },
    "all_completed": {
        "completed_at": "全链完成时刻（人类可读）",
        "auto_enhance_applied": "自动增强应用数（阶段6d）",
    },
    "pending_diagnosis": {},
}
def describe_stage_metrics_keys() -> dict:
    return {k: dict(v) for k, v in STAGE_METRICS_KEY_SPEC.items()}
PARSE_DEGRADE_EXC: tuple = (SyntaxError, ValueError, RecursionError,
                             MemoryError, TypeError)
LAYER_DEGRADE_EXC: tuple = PARSE_DEGRADE_EXC + (
    OSError, RuntimeError, KeyError, AttributeError)
LAYER_DEGRADE_EXC_WITH_IMPORT: tuple = LAYER_DEGRADE_EXC + (ImportError,)
METHOD_DEGRADE_EXC: tuple = LAYER_DEGRADE_EXC + (
    ImportError, ZeroDivisionError, IndexError)
MAX_SKILL_NAME_LENGTH = 64
SKILL_NAME_MIN_LEN = 2
DESC_MAX = 1024
SKILL_MD_LINE_LIMIT = 3500
LINE_LIMIT = SKILL_MD_LINE_LIMIT
ALLOWED_RESOURCES = {"scripts", "references", "assets", "tests"}
MAX_FILE_LINES = LINE_LIMIT
MAX_NESTING = Thresholds.NESTING_BLOCK
MAX_FUNC_LINES = _ROLE_FUNC_BUDGET_LINES
HARD_MAX_FILE_LINES = MAX_FILE_LINES
HARD_MAX_FUNC_LINES = MAX_FUNC_LINES
HARD_MAX_METHOD_LINES = MAX_FUNC_LINES
HARD_MAX_CLASS_LINES = _ROLE_CLASS_BUDGET_LINES
HARD_MAX_NESTING = MAX_NESTING
HARD_MAX_PARAMS = 7
SUB_ENGINE_META: dict[str, dict] = {
    "A1": {"main": "A", "legacy": "A1", "findings": True,
           "family": "AST-pattern", "types": ("ast",), "sub_modules": (
               "engine_a1_defects", "engine_a1_name_flow", "engine_a1_structure")},
    "A2": {"main": "A", "legacy": "A2", "findings": True,
           "family": "AST-antipattern", "types": ("metric", "manual"), "sub_modules": (
               "diag_health_scoring",)},
    "A3": {"main": "A", "legacy": "A3", "findings": True,
           "family": "AST-antipattern", "types": ("ast", "static_text"),
           "sub_modules": ("engine_a3_silent_degrade",)},
    "A4": {"main": "A", "legacy": "C2", "findings": True,
           "family": "static_text", "types": ("config", "static_text"),
           "sub_modules": ("engine_a4_doc_code",
                           "build_skill_md_optimize",
                           "build_skill_md_quality")},
    "B1": {"main": "B", "legacy": "B1", "findings": True,
           "family": "AST-antipattern", "types": ("ast", "static_text", "cohesion"),
           "sub_modules": ("engine_b2_history", "engine_b1_cohesion")},
    "B2": {"main": "B", "legacy": "B2", "findings": True,
           "family": "AST-verification", "types": ("history",),
           "sub_modules": ("engine_b2_history",)},
    "C1": {"main": "C", "legacy": "D1", "findings": True,
           "family": "call_graph", "types": ("call_graph", "dynamic", "resource"),
           "sub_modules": ("diag_exception_detection", "diag_exception_verdict",
                           "diag_method_invoke",
                           "diag_simulate_evidence",
                           "diag_simulate_runner",
                           "diag_simulate_sandbox",
                           "diag_structure_arch")},
    "D1": {"main": "D", "legacy": "E1", "findings": True,
           "family": "AST-security", "types": ("ast", "static_text", "resource"), "sub_modules": ("engine_d_security",)},
    "D2": {"main": "D", "legacy": "E2", "findings": True,
           "family": "AST-security", "types": ("ast", "dynamic"), "sub_modules": (
               "engine_d_security", "engine_d2_flow",
               "engine_d2_symbolic", "engine_d2_verdict")},
    "E1": {"main": "E", "legacy": "F1", "findings": True,
           "family": "runtime", "types": ("runtime", "coverage"), "sub_modules": ("testsuite_orchestrator",)},
    "E2": {"main": "E", "legacy": "F2", "findings": True,
           "family": "AST-complexity", "types": ("runtime", "dynamic"), "sub_modules": ("engine_e2_mutation",)},
    "E3": {"main": "E", "legacy": "F3", "findings": True,
           "family": "coverage", "types": ("test_quality", "coverage"),
           "sub_modules": ("diag_testing_static", "diag_testing_scan_ast",
                           "diag_testing_scan_sca",
                           "testsuite_coverage_map", "testsuite_registry")},
    "F1": {"main": "F", "legacy": "G1", "findings": False,
           "family": "AST-controlflow", "types": (),
           "sub_modules": ("treatment_plan",)},
    "F2": {"main": "F", "legacy": "G2", "findings": False,
           "family": "static_text", "types": (),
           "sub_modules": ("build_safe_orchestration",)},
    "F3": {"main": "F", "legacy": "G3", "findings": False,
           "family": "static_text", "types": (),
           "sub_modules": ("diag_delivery_gate",)},
    "F4": {"main": "F", "legacy": "G4", "findings": False,
           "family": "AST-verification", "types": (),
           "sub_modules": ("diag_regression_guard",)},
    "F5": {"main": "F", "legacy": "G5", "findings": False,
           "family": "", "types": (),
           "sub_modules": ("refactor_split_actions", "build_refactor_plan",
                           "fupan_analyzer")},
    "F6": {"main": "F", "legacy": "G6", "findings": False,
           "family": "", "types": (), "sub_modules": ("engine_f_deadcode",
                                                    "build_module_topology")},
}
LEGACY_TO_MAIN: dict[str, str] = {m["legacy"]: m["main"] for m in SUB_ENGINE_META.values()}
LEGACY_TO_SUB: dict[str, str] = {m["legacy"]: sid for sid, m in SUB_ENGINE_META.items()}
AGGREGATE_CV_TARGETS = frozenset({
    "CV-OVERALL-THRESHOLD",
    "CV-SUPPRESSION-RULES",
})
VULN_DESERIALIZATION = "deserialization"
VULN_RENDER_TEMPLATE_STRING = "render_template_string"
VULN_RENDER_TEMPLATE = "render_template"
class VulnerabilityCategory(Enum):
    SQL_INJECTION = "sql_injection"
    COMMAND_INJECTION = RULE_COMMAND_INJECTION
    DESERIALIZATION = VULN_DESERIALIZATION
    PATH_TRAVERSAL = "path_traversal"
    XSS = "xss"
    SSTI = "ssti"
    XXE = "xxe"
    LDAP_INJECTION = "ldap_injection"
    OPEN_REDIRECT = "open_redirect"
    WEAK_CRYPTO = "weak_crypto"
    HARDCODED_SECRET = RULE_HARDCODED_SECRET
    INSECURE_CONFIG = RULE_INSECURE_CONFIG
class DiagnoseSeverity(Enum):
    BLOCK = 'BLOCK'
    ERROR = 'ERROR'
    WARN = 'WARN'
    INFO = 'INFO'
POLYMORPHIC_METHODS = frozenset({'to_dict', 'to_json', 'to_html', 'to_csv', 'to_xml', 'from_dict', 'from_json', 'summary', 'diagnose', 'run', 'run_all', 'execute', 'scan', 'build', 'analyze', 'check', 'detect', 'collect', 'discover', 'start', 'stop', 'pause', 'resume', 'install', 'uninstall', 'snapshot', 'status', 'reset', 'close', 'cleanup', 'register', 'dispatch', 'handle', 'process', 'visit', 'generic_visit', 'get', 'post', 'put', 'delete', 'patch', 'configure', 'setup', 'teardown', 'init', 'is_clean', 'is_available', 'get_records', 'print_summary', 'get_uncovered', 'get_break_points', 'is_active', 'edge_count', 'get_by_severity', 'get_critical', 'get_dead_code', 'save_log'})
AST_VISITOR_PREFIXES = ('visit_',)
CLI_CMD_PREFIXES = ('cmd_',)
RESULT_STATUS_BUCKETS: frozenset[str] = frozenset(
    {'pass', 'warn', 'fail', 'skip', 'error'})
DEFAULT_CONFIDENCE_FALLBACK = 0.5
DEFAULT_FINDING_CONFIDENCE = 0.8
@dataclass
class GateThresholds:
    ARCH_MAX_FILE_REDUCTION_PCT: float = 30.0
    ARCH_MAX_FUNC_LINE: int = Thresholds.FUNC_LINES_BLOCK
    fragment_warn_dir_ratio: float = 0.40
    fragment_block_dir_ratio: float = 0.50
    fragment_min_lines: int = 80
    fragment_strict_mode: bool = True
    fragment_min_dir_files: int = 5
    FUNC_MIN_COVERAGE_PCT: float = 80.0
    FUNC_MIN_API_SURFACE_PCT: float = 95.0
    STUB_ABSOLUTE_SCOPE_TOTAL: int = 100
    IMPORT_MIN_INTEGRITY_PCT: float = 90.0
    IMPORT_SUBPROCESS_MIN_PASS_PCT: float = 95.0
    IMPORT_SUBPROCESS_TIMEOUT_S: int = 30
    STUB_MAX_RATIO_PCT: float = 30.0
    STUB_MAX_ABSOLUTE: int = 10
    SUBSYSTEM_MIN_PRESERVED_PCT: float = 80.0
    SIZE_LARGE_FILE_RATIO_MAX: float = 0.70
    SIZE_LARGE_FUNC_RATIO_WARN: float = 0.40
    ARCH_MAX_LINE_REDUCTION_PCT: float = 30.0
    AVG_LINES_WARN: int = 1000
    AVG_LINES_ALERT: int = HARD_MAX_FILE_LINES
class GuardLevel(Enum):
    INFO = "info"
    WARN = "warn"
    BLOCK = "block"
class OperationType(Enum):
    MODIFY_CODE = "modify_code"
    ADD_IMPORT = "add_import"
    REMOVE_CODE = "remove_code"
    WRITE_FILE = "write_file"
    DELETE_FILE = "delete_file"
    DELETE_DIR = "delete_dir"
    CLEANUP = "cleanup"
    REFACTOR = "refactor"
    MERGE = "merge"
    SPLIT = "split"
    RENAME = "rename"
    MOVE = "move"
class RuleDesc(str):
    def __new__(cls, desc, *, source_methods=None, severity="P2",
                category="confirmation"):
        instance = super().__new__(cls, desc)
        if isinstance(source_methods, bytes):
            source_methods = os.fsdecode(source_methods)
        if isinstance(source_methods, str):
            source_methods = (source_methods,) if source_methods else ()
        try:
            instance.source_methods = tuple(source_methods or ())
        except TypeError as _e:
            log_swallowed(__name__, _e, context='RuleDesc.__new__:TypeError')
            instance.source_methods = ()
        instance.severity = severity
        instance.category = category
        return instance
    def to_dict(self):
        try:
            return {
                "description": str(self),
                "source_methods": list(self.source_methods),
                "severity": self.severity,
                "category": self.category,
            }
        except Exception as e:
            logger.warning("to_dict: %s", e, exc_info=True)
            return {"_error": True, "_partial": True}
HUMAN_CONFIRM_RULE_ID = "规则31"
CV_RULES: dict[str, RuleDesc] = {
    "规则1":  RuleDesc("死代码确认 - D1(调用关系)+F1(覆盖率)", source_methods=["E","C"], severity="P1"),
    "规则2":  RuleDesc("安全确认 - B1+E1+F1(SCA)", source_methods=["E","B","D"], severity="P0", category="safety"),
    "规则3":  RuleDesc("复杂度确认 - B1+F1(复杂度)", source_methods=["E","B"], severity="P1"),
    "规则4":  RuleDesc("误报抑制 - B1+F1(单元测试覆盖率)", source_methods=["E","B"], severity="P1", category="meta"),
    "规则5":  RuleDesc("隐藏问题 - 测试失败+诊断未发现", source_methods=["E"], severity="P1", category="meta"),
    "规则6":  RuleDesc("语法错误 - A1(五维结构)+B1(静态解析)交叉", source_methods=["A","B"], severity="P0"),
    "规则7":  RuleDesc("循环依赖 - B1(cohesion CH01)+F1(集成)", source_methods=["E","B"], severity="P1"),
    "规则8":  RuleDesc("宽泛异常 - D1+B1+F1（broad_except 族专项确认）", source_methods=["E","C","B"], severity="P1"),
    "规则9":  RuleDesc("全局变量 - B1+F1(压力)", source_methods=["E","B"]),
    "规则10": RuleDesc("递归 - B1+F1(模糊)", source_methods=["E","B","C"]),
    "规则11": RuleDesc("调用断裂 - D1(调用图)+F1(E2E)", source_methods=["E","C"], severity="P1"),
    "规则12": RuleDesc("路径穿越 - E1+B1+F1(集成)", source_methods=["E","B","D"], severity="P0", category="safety"),
    "规则13": RuleDesc("大文件 - B1+F1(性能)", source_methods=["E","B"]),
    "规则14": RuleDesc("文件级多源确认 - 同一文件同一规则族被>=2个方法报告", severity="P1", category="meta"),
    "规则15": RuleDesc("单源自验证 - P0/P1单源->confirmed; P2单源: 通用>=0.85或AST源>=0.75->confirmed", severity="P1", category="meta"),
    "规则16": RuleDesc("矛盾检测 - 不同方法对同一指标矛盾时标记investigated", severity="P1", category="contradiction"),
    "规则17": RuleDesc("指标越界确认 - B1(AST)+B2(历史)交叉", source_methods=["B"]),
    "规则18": RuleDesc("门禁失败确认 - G3(交付门禁)+G2(守卫)交叉确认", source_methods=["F"], severity="P0"),
    "规则19": RuleDesc("基线退化确认 - B2(历史)+F1(回归)交叉确认", source_methods=["E","B"], severity="P1"),
    "规则20": RuleDesc("修复安全验证 - G1(自修复)+F1(回归)+G3(门禁)三向交叉确认", source_methods=["E","F"], severity="P0", category="safety"),
    "规则21": RuleDesc("动态导入确认 - B1(静态)+D1(运行时绑定)交叉", source_methods=["C","B"]),
    "规则22": RuleDesc("污点路径可行性 - E1安全漏洞+E2符号执行", source_methods=["D"], severity="P0", category="safety"),
    "规则23": RuleDesc("修复等价性 - G4修复产物独立复验（G1按设计不产出findings，本规则为纯G4专域）", source_methods=["F"], severity="P1"),
    "规则24": RuleDesc("日志异常确认 - B1(日志异常)+B1(反模式)+F1(冒烟)交叉", source_methods=["E","B"]),
    "规则25": RuleDesc("API兼容性确认 - B2(历史)+F1(兼容)+F1(回归)交叉", source_methods=["E","B"], severity="P1"),
    "规则26": RuleDesc("并发安全确认 - B1(并发分析)+A1/B1(AST)+F1(性能)", source_methods=["E","B"], severity="P1", category="safety"),
    "规则27": RuleDesc("文档一致性确认 - C2(文档-代码)交叉", source_methods=["A", "B"]),
    "规则28": RuleDesc("历史缺陷确认 - B2(缺陷模式)+B1(AST)+F1(回归)", source_methods=["E","B"]),
    "规则29": RuleDesc("突变覆盖确认 - F1(回归)+F2(定向突变)+B1(静态)交叉", source_methods=["E","B"]),
    "规则30": RuleDesc("历史趋势确认 - B2(历史分析)+F1(回归)交叉", source_methods=["E","B"]),
    HUMAN_CONFIRM_RULE_ID: RuleDesc("人工确认闭环 - HumanConfirmationStore应用历史确认/否决", severity="P1", category="meta"),
    "规则32": RuleDesc("配置漂移确认 - C2(文档一致性)+B1(AST)交叉", source_methods=["A","B"]),
    "规则33": RuleDesc("类型与测试质量 - B1(类型)+F1(测试质量)+F3(覆盖)交叉", source_methods=["E","B"]),
    "规则34": RuleDesc("隐式依赖确认 - B(AST)前置+C(调用图)/E(测试)交叉", source_methods=["E","C","B"]),
    "规则35": RuleDesc("多源降权确认 - B2(历史分析)+规则FP追踪+方法校准", source_methods=["B"], severity="P1", category="ranking"),
    "规则36": RuleDesc("语义级矛盾检测 - B1(大函数)+F1(复杂度)交叉", source_methods=["E","B"], category="contradiction"),
    "规则37": RuleDesc("历史基线差异对比 - 基线库(持续噪音降权)+规则15(单源衰减)", category="ranking"),
    "规则38": RuleDesc("业务流追踪验证 - 业务流可达性注解(xv_rule_checks 入口编排与可达遍历 + xv_evidence_channels 分诊注解)+规则1(死代码确认)交叉"),
    "规则39": RuleDesc("引用深度加权排序 - 引用深度注解(xv_ref_depth)+规则15(优先级修正)", category="ranking"),
    "规则40": RuleDesc("集群共识验证 - ensemble信号分析器+规则14(多源确认)增强版", category="meta"),
    "规则41": RuleDesc("变异测试确认 - F2(定向变异验证)+规则1(死代码确认)增强版"),
    "规则42": RuleDesc("性能热点确认 - F1(性能)+B1(并发)交叉", source_methods=["E","B"], severity="P1"),
    "规则43": RuleDesc("内存泄漏确认 - D1(资源泄漏)+F1(模糊)+F1(压力)交叉", source_methods=["E","C"], severity="P1", category="safety"),
    "规则44": RuleDesc("API向后兼容 - B2(历史)+F1(回归)+F1(兼容)交叉", source_methods=["E","B"], severity="P1"),
    "规则45": RuleDesc("测试有效性确认 - F1(测试质量)+F1(覆盖)+B1(死代码)交叉", source_methods=["E","B"]),
    "规则46": RuleDesc("代码可维护性 - B1(AST)+F1(复杂度)交叉", source_methods=["E","B"]),
    "规则47": RuleDesc("安全漏洞深度确认 - E1(安全)+E2(符号执行)+F1(SCA)交叉", source_methods=["E","D"], severity="P0", category="safety"),
    "规则48": RuleDesc("配置安全确认 - E1(安全)+F1(冒烟)+C2(文档)交叉", source_methods=["E","D","A"], severity="P1", category="safety"),
    "规则49": RuleDesc("类型注解确认 - B1(类型注解)自验证", source_methods=["A", "B"]),
    "规则50": RuleDesc("隐式依赖确认 - B1(隐式依赖)+D1(调用图)交叉", source_methods=["B","C"]),
    "规则51": RuleDesc("配置漂移交叉确认 - C2(文档一致性)交叉", source_methods=["A", "D"]),
    "规则52": RuleDesc("文件健康评分确认 - A1(五维分析)交叉", source_methods=["A", "B"], severity="P1"),
    "规则53": RuleDesc("结构性缺陷确认 - A1(结构性缺陷)+A1(AST检测)交叉", source_methods=["A", "B"], severity="P1"),
    "规则54": RuleDesc("拆分推荐确认 - A1(裁决)交叉", source_methods=["A", "B"]),
    "规则H1": RuleDesc("幻觉检测确认 - B1(H01-H08)+A1/A2 交叉验证幻觉API/导入/异常", source_methods=["A","B"], severity="P1"),
    "规则H2": RuleDesc("幻觉导入链验证 - H02: from X import *后_前缀符号+__all__验证", source_methods=["A","C","B"], severity="P1"),
    "规则H4": RuleDesc("幻觉上下文矛盾验证 - H04: 同文件前后逻辑矛盾", source_methods=["A","B"]),
    "规则H6": RuleDesc("测试幻觉验证 - H06: 变异测试识别假阳性测试", source_methods=["A","E"]),
    "规则H7": RuleDesc("记忆幻觉验证 - H07: 记忆'已实现'vs代码实际AST状态", source_methods=["A","B"], severity="P1"),
    "规则H8": RuleDesc("幻觉安全防护验证 - H08: 沙箱反射链检测", source_methods=["A","D"], severity="P0"),
    "规则55": RuleDesc("模块循环结构确认 - B1(cohesion_cycle硬环/软环)+A2(健康)交叉仲裁", source_methods=["B","A"], severity="P1"),
    "规则56": RuleDesc("[休眠:依赖已退役CH05] 模块拆分候选确认 - B1(cohesion_split超大文件独立块)+B1(复杂度)+A2(健康)交叉仲裁", source_methods=["B","A"]),
    "规则57": RuleDesc("[休眠:依赖已退役CH03/CH04] 模块迁移/合并候选确认 - B1(cohesion_migration错放符号/高覆盖文件)+A2交叉仲裁", source_methods=["B","A"], severity="P3"),
    "规则58": RuleDesc("VCS近变证据 - 版本控制近变(commit/mtime)注解+规则15(单源衰减)交叉", category="ranking"),
    "规则59": RuleDesc("反驳负证据分析 - 反证通道(counter_evidence)注解+规则16(矛盾检测)交叉"),
    "规则60": RuleDesc("测试触发定向冒烟 - 测试分诊(smoke pass/fail)注解+规则24(日志异常确认)交叉"),
    "规则61": RuleDesc("反向可证伪验证 - 可证伪性(verified/absent)注解+规则29(突变覆盖确认)交叉"),
}
SEVERITY_BLOCKING = "blocking"
SEVERITY_WARNING = "warning"
SEVERITY_INFO = "info"
KEY_SEVERITIES: tuple[str, ...] = (SEVERITY_BLOCKING, SEVERITY_WARNING)
WIRING_DECLARATION_ATTR = "wiring_declarations"
PREINTERVENTION_VERSION = "2.0.0"
MAX_FUNCTION_LINES = 200
MAX_FUNCTION_COMPLEXITY = Thresholds.CYCLOMATIC_BLOCK
MAX_CLASS_METHODS = 50
MAX_PARAMETERS = HARD_MAX_PARAMS
_CHECK_PROVIDERS = []
def register_check_provider(provider) -> None:
    if not callable(provider):
        raise TypeError(f"检查提供者必须可调用: {provider!r}")
    if provider not in _CHECK_PROVIDERS:
        _CHECK_PROVIDERS.append(provider)
def registered_check_providers() -> tuple:
    return tuple(_CHECK_PROVIDERS)
_REVIEW_PROVIDERS: dict[str, Any] = {}
def register_review_provider(name: str, provider: Any) -> None:
    key = name.strip() if isinstance(name, str) else ""
    if not key:
        raise ValueError(f"协作者名必须是非空 str: {name!r}")
    if not callable(provider):
        raise TypeError(f"协作者必须可调用: {provider!r}")
    _REVIEW_PROVIDERS[key] = provider
def registered_review_providers() -> dict[str, Any]:
    return dict(_REVIEW_PROVIDERS)
OUTPUT_TRUNCATE_LEN: int = 500
MESSAGE_TRUNCATE_LEN: int = 200
HASH_PREFIX_LEN: int = 16
CONFIRMED_DISPLAY_LIMIT: int = 20
MS_PER_SECOND: int = 1000
PERCENT_FACTOR: int = 100
TRACEBACK_TRUNCATE_LEN: int = 1000

#: 单个诊断方法（A～F）的时间预算（秒）。
#:
#: **单一真源**：方法执行、批量推进、锁等待、采集上限都从这里取值，
#: 不再各自写死数字。历史教训：``diag_method_invoke`` 写 2700，而
#: ``DEFAULT_BATCH_MAX_SECONDS`` 写 900、``DEFAULT_WAIT_TIMEOUT_S`` 写
#: 3600，任一环节短于方法真实耗时都会把「还在跑」误判成「超时降级」，
#: 结论直接作废（method_timeout）。307 模块规模下方法 B 实测 >45min，
#: 故统一提升到 2 小时。
#:
#: 可用环境变量 ``JWSGJ_METHOD_TIMEOUT_S`` 覆盖（见
#: ``diag_method_invoke.method_timeout_budget``）。
#:
#: 2026-11 二次调优：307 模块规模下方法 B（AST 核心检测）实测需要
#: 45～60 分钟，7200s（2 小时）余量偏紧；提升到 20000s（约 5.5 小时）
#: 以覆盖全量重扫 + 后续相位叠加。**四处派生常量均引用本值，
#: 不得再各自写死数字**。
DIAGNOSIS_METHOD_BUDGET_S: float = 20000.0
SOURCE_SEQUENCE_TYPES = (list, tuple, set, frozenset)
FINDING_LIST_KEYS: frozenset[str] = frozenset({
    "issues", "findings", "violations", "blindspots", "leaks",
    "hotspots", "complex_functions", RULE_HIGH_COMPLEXITY,
    "orphans", FIELD_RECOMMENDATIONS, "test_failures",
    "entries", "blindspot_entries", "implicit_deps",
    "security_issues", "antipatterns", "doc_mismatches",
    "vulnerabilities",
    "warnings", "smells",
    "tryceratops",
})
ANTIPATTERN_PREFIXES: frozenset[str] = frozenset({
    "C1_", "C2_", "C4_", "C6_", "C8_", "C11_", "C16_", "C17_",
    "C18_", "C19_",
})
STRUCTURED_PRIORITY_KEYS: tuple[str, ...] = (
    "_degradation_report", "final_html_reports", "fix_coverage", "by_strategy",
    "by_priority", "side_effect_summary", "treatment_items_preview",
    "changed_files",
)
STRUCTURED_EXCLUDED_KEYS: frozenset[str] = frozenset({
    "status", "elapsed_s", "summary", "message", "fix_plan",
})
def is_finding_carrier_key(key: Any) -> bool:
    if not isinstance(key, str):
        return False
    return (key in FINDING_LIST_KEYS
            or any(key.startswith(prefix) for prefix in ANTIPATTERN_PREFIXES))
SEVERITY_RANK: dict[str, int] = {
    "P0": 0, "CRITICAL": 0, "FATAL": 0, "BLOCK": 0,
    "P1": 1, "HIGH": 1, "ERROR": 1,
    "P2": 2, "MEDIUM": 2, "WARN": 2, "WARNING": 2,
    "P3": 3, "LOW": 3, "INFO": 3,
    "P4": 4,
}
SEVERITY_PENALTY_WEIGHTS: dict[str, int] = {
    "P0": 10, "P1": 5, "P2": 2, "P3": 1, "P4": 0,
}
DIAGNOSE_TO_P: dict[str, str] = {
    "BLOCK": "P0", "ERROR": "P1", "WARN": "P2", "INFO": "P3",
}
P_SCALE_LEVELS = frozenset(SEVERITY_PENALTY_WEIGHTS)
_P_LEVEL_BY_RANK: dict[int, str] = {
    rank: f"P{rank}" for rank in set(SEVERITY_RANK.values())
}
_SEVERITY_TEXT_TO_P: dict[str, str] = {
    **{word: _P_LEVEL_BY_RANK[rank]
       for word, rank in SEVERITY_RANK.items()},
    **DIAGNOSE_TO_P,
    SEVERITY_BLOCKING.upper(): "P0",
}
def diag_severity_to_p(sev: str | None) -> str:
    level = str(getattr(sev, "value", sev) or "").strip().upper()
    if level in P_SCALE_LEVELS:
        return level
    return _SEVERITY_TEXT_TO_P.get(level, "P3")
CONCLUSION_V2_MAP: dict[str, str] = {
    "confirmed": "confirmed",
    "suppressed": "suppressed",
    "likely": "likely",
    "uncertain": "uncertain",
    "contradictory": "contradictory",
    "investigated": "uncertain",
    "review": "uncertain",
    "reviewed": "uncertain",
}
FANOUT_STRATEGIES: tuple[str, ...] = (
    'code_migration',
    'unified_entry',
    'layer_boundary',
)
FANOUT_STRATEGY_LABELS: dict[str, str] = {
    'code_migration': '代码迁移',
    'unified_entry': '统一入口',
    'layer_boundary': '分层与边界调整',
}
FANOUT_STRATEGY_GOVERNANCE: dict[str, str] = {
    'code_migration': 'migrate_code',
    'unified_entry': 'converge_dependency',
    'layer_boundary': 'adjust_layer_boundary',
}
FANOUT_FORBIDDEN_ACTIONS: tuple[str, ...] = ('split_file', 'split_module')
@dataclass(frozen=True)
class FanoutGovernance:
    strategy: str
    priority: int
    label: str
    governance_method: str
    rationale: tuple[str, ...] = ()
    files: tuple[str, ...] = ()
    forbidden_actions: tuple[str, ...] = FANOUT_FORBIDDEN_ACTIONS
    def to_dict(self) -> dict:
        return {
            'strategy': self.strategy,
            'priority': self.priority,
            'label': self.label,
            'governance_method': self.governance_method,
            'rationale': list(self.rationale),
            'files': list(self.files),
            'forbidden_actions': list(self.forbidden_actions),
        }
FANOUT_LEVEL_L1 = 'L1'
FANOUT_LEVEL_L2 = 'L2'
FANOUT_LEVEL_L3 = 'L3'
FANOUT_LEVEL_L4 = 'L4'
FANOUT_LEVEL_UNKNOWN = 'unknown'
FANOUT_LEVEL_EXCLUDED = 'excluded'
FANOUT_LEVELS: tuple[str, ...] = (
    FANOUT_LEVEL_L1, FANOUT_LEVEL_L2, FANOUT_LEVEL_L3, FANOUT_LEVEL_L4,
)
_FANOUT_EXCLUDED_LABEL = '排除（包根/入口）'
FANOUT_LEVEL_LABELS: dict[str, str] = {
    FANOUT_LEVEL_L1: 'L1 健康',
    FANOUT_LEVEL_L2: 'L2 偏高',
    FANOUT_LEVEL_L3: 'L3 高风险',
    FANOUT_LEVEL_L4: 'L4 危机',
    FANOUT_LEVEL_UNKNOWN: '扇出未知',
    FANOUT_LEVEL_EXCLUDED: _FANOUT_EXCLUDED_LABEL,
}
FANOUT_ROLE_MODULE = 'module'
FANOUT_ROLE_ORCHESTRATOR = 'orchestrator_facade'
FANOUT_ROLE_UNMAPPED = 'unmapped'
FANOUT_ROLE_EXCLUDED = 'excluded'
FANOUT_ROLE_LABELS: dict[str, str] = {
    FANOUT_ROLE_MODULE: '普通模块',
    FANOUT_ROLE_ORCHESTRATOR: '编排/门面类',
    FANOUT_ROLE_UNMAPPED: '未映射',
    FANOUT_ROLE_EXCLUDED: _FANOUT_EXCLUDED_LABEL,
}
FANOUT_EXCLUDED_FILE_NAMES: frozenset[str] = frozenset({
    '__init__.py', '__main__.py',
})
def is_fanout_excluded_file(file_path: Any) -> bool:
    normalized = normalize_filepath(file_path)
    if not normalized:
        return False
    name = os.path.basename(normalized.replace('\\', '/')).lower()
    return name in FANOUT_EXCLUDED_FILE_NAMES
def _fanout_row_filepath(row: dict) -> str:
    return (normalize_filepath(row.get('file'))
            or normalize_filepath(row.get('module')))
FANOUT_ORCHESTRATOR_MODULES: dict[str, str] = {
    'xv_confidence_review': '阶段2b 交叉验证执行与收尾编排',
    'ai_review_governance': 'AI 审核治理与裁决执行组合根',
    'build_preflight': '预检—创建—创建后观测编排',
    'treatment_feedback': '阶段6b 治疗反馈闭环编排',
    'refactor_split_actions': '拆分动作编排宿主',
    'fupan_engine': '复盘评审引擎编排',
    'engine_f_deadcode': 'F 组执行编排',
    'diag_split_gate': '五重写前门禁编排',
    'build_skill_quality_a2': 'A 组引擎编排',
    'build_skill_lifecycle': '生命周期与只读体检编排',
    'skill_doc_refactor_guard': '技能文档重构与写回守卫',
    'diag_antipattern_flow_detect': '反模式检测通道与结果归一',
    'diag_antipattern_flow_govern': '反模式消除与循环耦合治理',
}
FANOUT_ORCHESTRATOR_NAME_TOKENS: frozenset[str] = frozenset({
    'orchestrator', 'orchestration', 'pipeline', 'facade', 'assembly',
    'composition', 'compose', 'coordinator', 'dispatcher', 'scheduler',
    'router', 'runner', 'entry', 'entrypoint', 'bootstrap', 'cli', 'surface',
})
_FANOUT_ROLE_SPLIT_RE = re.compile(r'[._\-]+')
FANOUT_BAND_TABLE: dict[str, tuple[tuple[str, int, int | None], ...]] = {
    FANOUT_ROLE_MODULE: (
        (FANOUT_LEVEL_L1, 0, 4),
        (FANOUT_LEVEL_L2, 5, 7),
        (FANOUT_LEVEL_L3, 8, 15),
        (FANOUT_LEVEL_L4, 16, None),
    ),
    FANOUT_ROLE_ORCHESTRATOR: (
        (FANOUT_LEVEL_L1, 0, 10),
        (FANOUT_LEVEL_L2, 11, 15),
        (FANOUT_LEVEL_L3, 16, 25),
        (FANOUT_LEVEL_L4, 26, None),
    ),
}
def _fanout_bands_of(role: str) -> tuple[tuple[str, int, int | None], ...]:
    role = coerce_fanout_role(role) or FANOUT_ROLE_MODULE
    if role == FANOUT_ROLE_EXCLUDED:
        return ()
    return FANOUT_BAND_TABLE.get(
        role, FANOUT_BAND_TABLE[FANOUT_ROLE_MODULE])
def _fanout_span_text(lower: int, upper: int | None) -> str:
    if upper is None:
        return f'>{lower - 1}'
    return f'{lower}-{upper}'
def fanout_band_text(role: str = FANOUT_ROLE_MODULE) -> str:
    return ' / '.join(
        f'{level} {_fanout_span_text(lower, upper)}'
        for level, lower, upper in _fanout_bands_of(role))
FANOUT_LEVEL_THRESHOLDS: dict[str, dict[str, tuple[int, int | None]]] = {
    role: {level: (lower, upper) for level, lower, upper in bands}
    for role, bands in FANOUT_BAND_TABLE.items()
}
FANOUT_LEVEL_BANDS: dict[str, tuple[tuple[int | None, str], ...]] = {
    role: tuple((upper, level) for level, _lower, upper in bands)
    for role, bands in FANOUT_BAND_TABLE.items()
}
def _fanout_threshold_of_role(role: str) -> int:
    if role == FANOUT_ROLE_EXCLUDED:
        return 0
    bands = FANOUT_BAND_TABLE.get(role, FANOUT_BAND_TABLE[FANOUT_ROLE_MODULE])
    return bands[-1][1] - 1
FANOUT_THRESHOLD_PROFILE: dict[str, int] = {
    role: _fanout_threshold_of_role(role) for role in FANOUT_ROLE_LABELS
}
FANOUT_DEPENDENCY_THRESHOLD = FANOUT_THRESHOLD_PROFILE[FANOUT_ROLE_MODULE]
FANOUT_ORCHESTRATOR_DEPENDENCY_THRESHOLD = (
    FANOUT_THRESHOLD_PROFILE[FANOUT_ROLE_ORCHESTRATOR])
def coerce_fanout_role(role: Any) -> str:
    if not isinstance(role, str):
        return ""
    text = role.strip().lower()
    return text if text in FANOUT_ROLE_LABELS else ""
def coerce_fanout_level(level: Any) -> str:
    if not isinstance(level, str):
        return ""
    text = level.strip()
    upper = text.upper()
    if upper in FANOUT_LEVELS:
        return upper
    lower = text.lower()
    if lower in (FANOUT_LEVEL_UNKNOWN, FANOUT_LEVEL_EXCLUDED):
        return lower
    return ""
def fanout_threshold_of(role: str) -> int:
    role = coerce_fanout_role(role) or FANOUT_ROLE_MODULE
    return FANOUT_THRESHOLD_PROFILE.get(role, FANOUT_DEPENDENCY_THRESHOLD)
def _fanout_scope_text(*, strict: bool) -> str:
    parts = []
    for role in (FANOUT_ROLE_MODULE, FANOUT_ROLE_ORCHESTRATOR):
        limit = fanout_threshold_of(role)
        span = f'>{limit}' if strict else f'0-{limit}'
        parts.append(f'{FANOUT_ROLE_LABELS[role]} {span}')
    return ' / '.join(parts)
def fanout_mandatory_scope_text() -> str:
    return _fanout_scope_text(strict=True)
def fanout_advisory_scope_text() -> str:
    return _fanout_scope_text(strict=False)
def classify_fanout_role(module_name: str, *, is_package: bool = False,
                         is_entry: bool = False,
                         orchestrator_modules: dict[str, str] | None = None) -> str:
    if is_package or is_entry:
        return FANOUT_ROLE_EXCLUDED
    name = module_name if isinstance(module_name, str) else ''
    leaf = name.rsplit('.', 1)[-1]
    roster = (FANOUT_ORCHESTRATOR_MODULES if orchestrator_modules is None
              else orchestrator_modules)
    if name in roster or leaf in roster:
        return FANOUT_ROLE_ORCHESTRATOR
    tokens = {
        token for token in _FANOUT_ROLE_SPLIT_RE.split(name) if token
    }
    if tokens & FANOUT_ORCHESTRATOR_NAME_TOKENS:
        return FANOUT_ROLE_ORCHESTRATOR
    return FANOUT_ROLE_MODULE if tokens else FANOUT_ROLE_UNMAPPED
def classify_fanout_level(degree: Any, role: str = FANOUT_ROLE_MODULE) -> str:
    role = coerce_fanout_role(role) or FANOUT_ROLE_MODULE
    if role == FANOUT_ROLE_EXCLUDED:
        return FANOUT_LEVEL_EXCLUDED
    value = fanout_degree_of(degree)
    if value is None or value < 0:
        return FANOUT_LEVEL_UNKNOWN
    bands = FANOUT_LEVEL_BANDS.get(
        role, FANOUT_LEVEL_BANDS[FANOUT_ROLE_MODULE])
    for upper, level in bands:
        if upper is None or value <= upper:
            return level
    return FANOUT_LEVEL_L4
def fanout_level_is_mandatory(level: str) -> bool:
    return coerce_fanout_level(level) == FANOUT_LEVEL_L4
def fanout_level_label(level: str) -> str:
    return FANOUT_LEVEL_LABELS.get(
        coerce_fanout_level(level), FANOUT_LEVEL_LABELS[FANOUT_LEVEL_UNKNOWN])
FANOUT_GOVERNANCE_RULE = (
    '模块级内部扇出按角色分档：'
    f'普通模块 {fanout_band_text(FANOUT_ROLE_MODULE)}；'
    f'编排/门面类 {fanout_band_text(FANOUT_ROLE_ORCHESTRATOR)}；'
    'L4 强制治理，L1-L3 由 AI 分析并做方案对比'
    '（pros/cons/net_benefit）后决定治理或留痕；'
    '包根 __init__.py 与入口 __main__.py 排除在治理面之外。'
)
FANOUT_TIER_MANDATORY = 'mandatory'
FANOUT_TIER_ADVISORY = 'advisory'
FANOUT_TIER_UNKNOWN = 'unknown'
FANOUT_TIER_EXCLUDED = 'excluded'
def fanout_degree_of(value: Any) -> int | None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return None
    if isinstance(value, float) and not value.is_integer():
        return None
    return int(value)
def resolve_fanout_degree(source: Any) -> int | None:
    data = source if isinstance(source, dict) else {}
    primary = fanout_degree_of(data.get('module_dependency_fanout'))
    if primary is not None and primary >= 0:
        return primary
    fallback = fanout_degree_of(data.get('dependency_fanout'))
    if fallback is not None and fallback >= 0:
        return fallback
    return primary if primary is not None else fallback
def _first_governance_text(*values: Any) -> str:
    for value in values:
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ''
def resolve_fanout_governance_level(source: Any) -> str:
    data = source if isinstance(source, dict) else {}
    if is_fanout_excluded_file(_fanout_row_filepath(data)):
        return FANOUT_LEVEL_EXCLUDED
    role = coerce_fanout_role(data.get('module_role'))
    if role == FANOUT_ROLE_EXCLUDED:
        return FANOUT_LEVEL_EXCLUDED
    tier = _first_governance_text(
        data.get('module_governance_tier'), data.get('governance_tier')).lower()
    if tier == FANOUT_TIER_EXCLUDED:
        return FANOUT_LEVEL_EXCLUDED
    level = coerce_fanout_level(_first_governance_text(
        data.get('module_governance_level'), data.get('governance_level')))
    if level and level != FANOUT_LEVEL_UNKNOWN:
        return level
    degree = resolve_fanout_degree(data)
    if degree is not None:
        return classify_fanout_level(degree, role or FANOUT_ROLE_MODULE)
    if level == FANOUT_LEVEL_UNKNOWN:
        return FANOUT_LEVEL_UNKNOWN
    if tier == FANOUT_TIER_MANDATORY:
        return FANOUT_LEVEL_L4
    if tier == FANOUT_TIER_ADVISORY:
        return FANOUT_LEVEL_L1
    return FANOUT_LEVEL_UNKNOWN
def finalize_fanout_module_governance(row: dict) -> None:
    if not isinstance(row, dict):
        return
    raw_role = row.get('module_role')
    role = coerce_fanout_role(raw_role)
    if is_fanout_excluded_file(_fanout_row_filepath(row)):
        role = FANOUT_ROLE_EXCLUDED
    elif not role:
        role = (FANOUT_ROLE_UNMAPPED
                if isinstance(raw_role, str) and raw_role.strip()
                else FANOUT_ROLE_MODULE)
    row['module_role'] = role
    row['module_role_label'] = FANOUT_ROLE_LABELS[role]
    level = resolve_fanout_governance_level(row)
    if level == FANOUT_LEVEL_EXCLUDED:
        role = FANOUT_ROLE_EXCLUDED
        row['module_role'] = role
        row['module_role_label'] = FANOUT_ROLE_LABELS[role]
    row['governance_level'] = level
    row['governance_label'] = fanout_level_label(level)
    row['governance_tier'] = (
        FANOUT_TIER_UNKNOWN if level == FANOUT_LEVEL_UNKNOWN
        else FANOUT_TIER_EXCLUDED if level == FANOUT_LEVEL_EXCLUDED
        else (FANOUT_TIER_MANDATORY if fanout_level_is_mandatory(level)
              else FANOUT_TIER_ADVISORY))
    row['mandatory'] = fanout_level_is_mandatory(level)
    row['governance_threshold'] = fanout_threshold_of(role)
    row['governance_thresholds'] = dict(FANOUT_THRESHOLD_PROFILE)
    row['governance_basis'] = 'module_import_fanout'
    row['governance_rule'] = FANOUT_GOVERNANCE_RULE
    row['benefit_required'] = level != FANOUT_LEVEL_EXCLUDED
HIGH_SEVERITY_PROTECTED = frozenset(
    _sev for _sev, _rank in SEVERITY_RANK.items() if _rank <= 1
)
RULE_FAMILY_MAP: dict[str, str] = {
    "BE-01": "broad_except", "broad_except": "broad_except",
    "EX-01": "broad_except", "bare_except": "broad_except",
    "EH-01": "empty_except", "empty_except": "empty_except",
    "BUG-003": "sql_injection",
    "SZ-01": "high_complexity", "SZ-02": "high_complexity",
    "long_function": "high_complexity", "large_range": "high_complexity",
    "deep_nesting": "high_complexity", "nested_loop": "high_complexity",
    "too_many_params": "high_complexity", "high_rfc": "high_complexity",
    "DC-01": "dead_code", "DC-02": "dead_code", "DC-03": "dead_code",
    "unreachable_code": "dead_code", "unused_definition": "dead_code",
    "dead_code_increase": "dead_code", "orphan_increase": "dead_code",
    "orphan_module": "dead_code",
    "standalone_unimported": "dead_code",
    "standalone_unreachable": "dead_code",
    "orphan": "dead_code",
    "public_untested": "low_coverage",
    "dead_stub": "dead_code",
    "empty_shell": "dead_code",
    "no_test_coverage": "low_coverage",
    "dead_module": "dead_code",
    "cli_entry_unexecuted": "dead_code",
    "empty_function": "dead_code",
    "stub_function": "dead_code",
    "pass_stub": "dead_code",
    "dead_code_block": "dead_code",
    "undertested": "low_coverage",
    "dynamic_binding": "dead_code",
    "cycle_module": "circular_dep",
    "exception_swallow": "empty_except",
    "DOC-MISSING": "doc_consistency",
    "DOC-ORPHAN": "doc_consistency",
    "DOC-ALL-GHOST": "doc_consistency",
    "C6_circular": "circular_dep",
    "circular_dependency": "circular_dep", "new_circular_import": "circular_dep",
    "GF-08": "broken_call", "broken_cross_call": "broken_call",
    "breakpoint_increase": "broken_call",
    "mutable_global": "mutable_global", "shared_mutable_state": "mutable_global",
    "excessive_global_state": "mutable_global",
    "mutable_default": "mutable_default", "RB-01": "mutable_default",
    "trivial_delegation": "trivial_delegation", "PF01": "trivial_delegation",
    "O04": "trivial_delegation", "D50": "trivial_delegation",
    "D51": "trivial_delegation",
    "C19_passthrough_layer": "trivial_delegation",
    "AP-C19": "trivial_delegation",
    "SE-06": "path_traversal", "path_traversal": "path_traversal", "PT-01": "path_traversal",
    "duplicate_code": "duplicate_code", "duplicate_string": "duplicate_code",
    "C18_default_duplication": "duplicate_code",
    "AP-C18": "duplicate_code",
    "unused_import": "unused_import",
    "missing_docstring": "missing_docstring",
    "shadowing_builtin": "shadowing_builtin",
    "global_statement": "global_statement",
    "none_comparison": "code_smell", "self_assignment": "code_smell",
    "constant_comparison": "code_smell", "todo_marker": "code_smell",
    "string_concat_in_loop": "code_smell", "module_level_call": "code_smell",
    "hardcoded_credential": "hardcoded_credential", "danger_pattern": "danger_pattern",
    "hardcoded_cred": "hardcoded_credential",
    "none_compare": "code_smell",
    "tm_survived": "test_smell",
    "ex_swallowed": "empty_except",
    "test_failure": "test_failure", "test_failures": "test_failure",
    "test_error": "test_error", "test_smell": "test_smell",
    "no_assertions": "test_smell", "assert_in_production": "test_smell",
    "empty_test_file": "test_smell", "low_mutation_score": "test_smell",
    "god_module": "architecture", "fat_interface": "architecture",
    "srp_violation": "architecture", "ocp_violation": "architecture",
    "layer_violation": "architecture", "dependency_direction": "architecture",
    "dependency_inversion": "architecture", "excessive_coupling": "architecture",
    "low_cohesion": "architecture", "transitive_coupling": "architecture",
    "unstable_dependency": "architecture",
    "deprecated_api": "compatibility", "version_incompatibility": "compatibility",
    "deprecated_stdlib": "compatibility",
    "unnecessary_coding_decl": "compatibility",
    "signature_change": "compatibility",
    "api_removed_functions": "api_change", "api_removed_classes": "api_change",
    "api_added_functions": "api_change",
    "score_regression": "regression", "blindspot_increase": "regression",
    "all_inconsistency": "regression", "new_files": "regression",
    "relative_import": "regression", "naming_cluster": "regression",
    "unbounded_recursion": "unbounded_recursion",
    "syntax_error": "syntax_error",
    "AI-01": "api_issue", "AI-02": "api_issue", "AI-03": "api_issue",
    "AI-04": "api_issue", "AI-05": "api_issue", "AI-06": "api_issue",
    "AI-07": "api_issue", "AI-08": "api_issue",
    "GF-07": "god_file", "GF-11": "god_file", "GF-13": "god_file",
    "AP-C1": "facade_antipattern", "AP-C2": "lazy_import",
    "AP-C4": "regression", "AP-C8": "dead_code",
    "AP-C11": "duplicate_code", "AP-C6": "circular_dep",
    "AP-C16": "dead_code", "AP-C17": "dynamic_import",
    "cycle_impact": "circular_dep",
    "lazy_import": "lazy_import",
    "SE-20": "danger_pattern",
    "SE-04": "insecure_deserialization",
    "DiagnoseFinding": "diag_general",
    "SN-01": "silent_swallow", "SN-02": "silent_swallow",
    "SN-03": "silent_swallow", "SN-04": "silent_swallow",
    "SD-01": "silent_swallow", "SD-02": "silent_swallow",
    "SD-03": "silent_swallow", "SD-04": "silent_swallow",
    "SD-05": "silent_swallow",
    "LP-01": "liveness_probe", "LP-02": "liveness_probe",
    "LP-03": "liveness_probe", "LP-04": "liveness_probe",
    "BE-02": "broad_except", "BE-03": "broad_except",
    "BE-04": "broad_except", "BE-05": "broad_except",
    "SE-01": "danger_pattern", "SE-02": "danger_pattern",
    "SE-03": "hardcoded_credential", "SE-05": "danger_pattern",
    "SE-07": "danger_pattern",
    "SE-08": "danger_pattern",
    "SE-09": "danger_pattern",
    "SE-10": "danger_pattern",
    "SE-11": "danger_pattern",
    "SE-12": "danger_pattern",
    "SE-13": "danger_pattern",
    "SE-14": "danger_pattern",
    "SE-15": "danger_pattern",
    "SE-16": "danger_pattern",
    "SE-17": "danger_pattern",
    "SE-18": "danger_pattern",
    "SE-19": "danger_pattern",
    "SE-23": "danger_pattern", "SE-24": "danger_pattern",
    "SE-25": "danger_pattern", "SE-26": "danger_pattern",
    "SE-27": "danger_pattern", "SE-28": "danger_pattern",
    "SE-29": "danger_pattern", "SE-30": "danger_pattern",
    "SE-31": "danger_pattern",
    "SE-32": "danger_pattern",
    "SE-33": "danger_pattern", "SE-34": "danger_pattern",
    "SE-35": "danger_pattern", "SE-36": "danger_pattern",
    "SE-37": "danger_pattern",
    "SE-38": "danger_pattern", "SE-39": "danger_pattern",
    "SE-40": "danger_pattern",
    "SE-30b": "danger_pattern",
    "DC-04": "dead_code", "DC-05": "dead_code", "DC-06": "dead_code",
    "circular_import": "circular_dep",
    "over_limit": "god_file",
    "undefined_name": "undefined_name",
    "all_overwrite": "api_issue",
    "suspicious_naming": "code_smell",
    "duplicate_import": "unused_import",
    "C2": "high_complexity",
    "priority_recommendation": "priority_rec",
    "unreachable_after_return": "dead_code",
    "method_anomaly": "method_anomaly",
    "method_pass": "method_pass",
    "low_coverage": "low_coverage",
    "orphan_function": "orphan_function",
    "dead_code": "dead_code",
    "sim_failed": "sim_failure",
    "perf_hotspot": "perf_hotspot",
    "high_complexity": "high_complexity",
    "low_health_score": "health_score",
    "low_quality_score": "quality_score",
    "high_coupling": "high_coupling",
    "cohesion": "cohesion",
    "cohesion_cycle": "cohesion_cycle",
    "cohesion_split": "cohesion_split",
    "cohesion_migration": "cohesion_migration",
    "large_codebase": "large_codebase",
    "empty_project": "empty_project",
    "no_guards_registered": "gate_issue",
    "gate_failed": "gate_issue",
    "gate_blockers": "gate_issue",
    "resource_leak": "resource_leak",
    "fix_safety_issue": "fix_safety",
    "fix_suggestion": "fix_safety",
    "quadrant_dead": "dead_code",
    "quadrant_dynamic": "dead_code",
    "quadrant_undertested": "low_coverage",
    "memory_leak": "resource_leak",
    "file_leak": "resource_leak",
    "connection_leak": "resource_leak",
    "handle_leak": "resource_leak",
    "breaking_change": "compatibility",
    "test_quality": "test_quality",
    "config_drift": "config_drift",
    "insecure_config": "config_drift",
    "missing_config": "config_drift",
    "config_error": "config_drift",
    "unsafe_eval": "danger_pattern",
    "command_injection": "danger_pattern",
    "xxe": "danger_pattern",
    "ssrf": "danger_pattern",
    "csrf": "danger_pattern",
    "weak_crypto": "danger_pattern",
    "insecure_random": "danger_pattern",
    "infinite_loop": "perf_hotspot",
    "dependency_vulnerability": "dependency_vulnerability",
    "e2e_failure": "e2e_failure",
    "fuzz_crash": "fuzz_crash",
    "smoke_failure": "smoke_failure",
    "stress_issue": "stress_issue",
    "blindspot": "dead_code", "BLINDSPOT": "dead_code",
    "dead_code_confirmed": "dead_code",
    "antipattern": "facade_antipattern", "C1_facade": "facade_antipattern",
    "concurrency": "liveness_probe", "CS-UNPROTECTED": "liveness_probe",
    "race_condition": "liveness_probe", "thread_safety": "liveness_probe",
    "historical_pattern": "dead_code", "HP-006": "dead_code", "HP-003": "dead_code", "HP-001": "dead_code", "HP-002": "dead_code",
    "D17-PRINT-AS-LOG": "broad_except", "D17-ERROR-IN-LOOP": "broad_except",
    "D17-LEVEL-MISUSE": "broad_except", "log_misuse": "broad_except",
    "type_annotation": "type_check", "TY-01": "type_check",
    "missing_type_annotation": "type_check", "missing_annotations": "type_check",
    "D21-CROSS-MODULE-ASSIGN": "dynamic_import", "D21-IMPORTLIB": "dynamic_import",
    "D21-SYS-MODULES": "dynamic_import", "D21-INIT-SIDE-EFFECT": "dynamic_import",
    "implicit_dep": "dynamic_import",
    "ast_rule": "diag_general",
    "independent_check": "diag_general",
    "security_vuln": "danger_pattern",
    "delivery_gate": "gate_issue",
    "large_file": "god_file",
    "CR-004": "code_smell",
    "doc_code_mismatch": "doc_consistency",
    "ruff_style": "code_smell", "RUFF-I001": "code_smell",
    "RUFF-F401": "dead_code", "RUFF-F811": "dead_code",
    "RUFF-E501": "code_smell", "RUFF-W291": "code_smell",
    "BANDIT-B324": "danger_pattern", "BANDIT-B603": "danger_pattern",
    "BANDIT-B105": "hardcoded_credential", "BANDIT-B607": "danger_pattern",
    "BANDIT-B404": "danger_pattern", "BANDIT-B311": "code_smell",
    "BANDIT-B102": "code_smell", "BANDIT-B403": "danger_pattern",
    "BANDIT-B301": "danger_pattern", "BANDIT-B108": "code_smell",
    "static_check": "diag_general",
    "security_pattern": "danger_pattern",
    "complexity": "high_complexity",
    "perf_issue": "perf_hotspot",
    "AST-lint": "code_smell",
    "AST-pattern": "diag_general",
    "AST-controlflow": "diag_general",
    "AST-antipattern": "facade_antipattern",
    "AST-verification": "dead_code",
    "AST-security": "danger_pattern",
    "AST-complexity": "high_complexity",
    "AST-resource": "resource_leak",
    "static_text": "doc_consistency",
    "dynamic_exec": "perf_hotspot",
    "metrics": "high_complexity",
    "log_analysis": "broad_except",
    "type_check": "type_check",
    "coverage": "low_coverage",
    "runtime": "sim_failure",
    "hallucinated_api": "hallucination", "hallucinated_import": "hallucination",
    "hallucinated_module": "hallucination",
    "hallucinated_exception": "hallucination", "context_contradiction": "hallucination",
    "ai_slop": "hallucination", "test_illusion": "hallucination",
    "memory_hallucination": "hallucination", "sandbox_reflection": "hallucination",
    "hallucination_general": "hallucination",
}
ALL_FAMILY_KEYS: frozenset[str] = frozenset(RULE_FAMILY_MAP.keys()) | frozenset(RULE_FAMILY_MAP.values())
SHARED_BASE_CONSUMER_THRESHOLD = 5
DEFAULT_VIRTUAL_FILENAME = "<unknown>"
RETRO_SCORE_DIMENSIONS: tuple[tuple[str, str, float], ...] = (
    ("diagnosis_quality", "诊断质量", 0.25),
    ("cv_accuracy", "交叉验证准确性", 0.20),
    ("treatment_effectiveness", "治疗有效性", 0.25),
    ("side_effect_control", "副作用控制", 0.15),
    ("feedback_loop_quality", "反馈闭环质量", 0.15),
)
MEMORY_WRITE_ACTIONS: frozenset[str] = frozenset({"add", "patch"})
__all__ = [  # noqa: RUF022
    "DEFAULT_VIRTUAL_FILENAME",
    "MEMORY_WRITE_ACTIONS",
    "LOW_RELIABILITY_BASE",
    "ALL_FAMILY_KEYS",
    "RULE_FAMILY_MAP",
    "AUTO_THRESHOLD_DECAY",
    "CONF_BOOST_MODERATE",
    "CONF_BOOST_SMALL",
    "CONF_BOOST_STEP",
    "CONF_CAP",
    "CONF_DEFAULT_PENALTY",
    "CONF_FLOOR",
    "CONF_LOW",
    "CONF_MEDIUM",
    "CONF_HIGH",
    "CONF_VERY_HIGH",
    "CONF_PENALTY_MODERATE",
    "FP_RATE_CRITICAL",
    "FP_RATE_HIGH",
    "FP_RATE_LOW",
    "FP_RATE_MEDIUM",
    "FP_RATE_VERY_LOW",
    "METHOD_SUB_RULES",
    "SIGNAL_BASELINE_HIT_COUNT",
    "SIGNAL_BASELINE_PERSISTENT_NOISE",
    "SIGNAL_BIZFLOW_CONFIDENCE_BOOST",
    "SIGNAL_DEGRADE_FACTOR",
    "SIGNAL_ENSEMBLE_GROUP_COUNT",
    "SIGNAL_ENSEMBLE_LOW_CONFIDENCE",
    "SIGNAL_PARTIAL_SOURCES",
    "SIGNAL_REFDEPTH_CHAIN_DEPTH",
    "SIGNAL_REFDEPTH_CONFIDENCE_BOOST",
    "SIGNAL_REFDEPTH_IN_DEGREE",
    "SIGNAL_REFDEPTH_ISOLATED",
    "SIGNAL_REFDEPTH_PRIORITY_BOOST",
    "SIGNAL_STAGE1_FP_CANDIDATE",
    "SIGNAL_STATS_DRIVEN_CANDIDATE",
    'AGGREGATE_CV_TARGETS',
    'ALLOWED_RESOURCES',
    'ANTIPATTERN_PREFIXES',
    'AST_VISITOR_PREFIXES',
    'PROJECT_ROOT_MARKERS',
    'CAT_CROSS_VALIDATION',
    'CAT_DISCOVERABILITY',
    'CAT_DYNAMIC_BINDING',
    'CAT_DYNAMIC_DISPATCH',
    'CAT_DYNAMIC_IMPORTS',
    'CAT_EXCEPTION_HANDLING',
    'CAT_MAINTAINABILITY',
    'SPLIT_SAFETY_DIMENSION',
    'CLI_CMD_PREFIXES',
    'CODING_UTF8',
    'CONCLUSION_V2_MAP',
    'CONFIRMED_DISPLAY_LIMIT',
    'CV_RULES',
    'CodeRegion',
    'D_ARCH_RULE_SUGGESTIONS',
    'DEFAULT_CONFIDENCE_FALLBACK',
    'DEFAULT_FINDING_CONFIDENCE',
    'DEFAULT_SESSION_QUOTA',
    'DEFAULT_TASK_TYPE',
    'DESC_MAX',
    'DIAGNOSE_TO_P',
    'DIAG_REPORT_DIRNAME',
    'DiagnoseSeverity',
    'EntryDecision',
    'FANOUT_BAND_TABLE',
    'FANOUT_DEPENDENCY_THRESHOLD',
    'FANOUT_EXCLUDED_FILE_NAMES',
    'FANOUT_FORBIDDEN_ACTIONS',
    'FANOUT_GOVERNANCE_RULE',
    'FANOUT_LEVEL_BANDS',
    'FANOUT_LEVEL_EXCLUDED',
    'FANOUT_LEVEL_L1',
    'FANOUT_LEVEL_L2',
    'FANOUT_LEVEL_L3',
    'FANOUT_LEVEL_L4',
    'FANOUT_LEVEL_LABELS',
    'FANOUT_LEVEL_THRESHOLDS',
    'FANOUT_LEVEL_UNKNOWN',
    'FANOUT_LEVELS',
    'FANOUT_ORCHESTRATOR_DEPENDENCY_THRESHOLD',
    'FANOUT_ORCHESTRATOR_MODULES',
    'FANOUT_ORCHESTRATOR_NAME_TOKENS',
    'FANOUT_ROLE_EXCLUDED',
    'FANOUT_ROLE_LABELS',
    'FANOUT_ROLE_MODULE',
    'FANOUT_ROLE_ORCHESTRATOR',
    'FANOUT_ROLE_UNMAPPED',
    'FANOUT_STRATEGIES',
    'MANDATORY_PIPELINE_TRIGGER_KEYWORDS',
    'FANOUT_STRATEGY_GOVERNANCE',
    'FANOUT_STRATEGY_LABELS',
    'FANOUT_THRESHOLD_PROFILE',
    'FANOUT_TIER_ADVISORY',
    'FANOUT_TIER_EXCLUDED',
    'FANOUT_TIER_MANDATORY',
    'FANOUT_TIER_UNKNOWN',
    'FanoutGovernance',
    'FIELD_ADJUSTED_CONFIDENCE',
    'FIELD_BASE_CONFIDENCE',
    'FIELD_CAPABILITY_COVERAGE',
    'FIELD_CODE_LEVEL_FEEDBACK',
    'FIELD_CV_CONFIDENCE_THRESHOLDS',
    'FIELD_CV_RULE_WEIGHTS',
    'FIELD_DIAGNOSIS_METHOD',
    'FIELD_DISCOVERABILITY_INDEX',
    'FIELD_EVIDENCE_FAMILIES',
    'FIELD_EVIDENCE_STRENGTH',
    'FIELD_EXECUTION_ERROR',
    'FIELD_EXPECTED_IMPACT',
    'FIELD_FALSE_NEGATIVE_RISK',
    'FIELD_FINDINGS_SUPPRESSED',
    'FIELD_FROZEN_ROUNDS_REMAINING',
    'FIELD_INTERMEDIATE_REPORTS',
    'FIELD_METHODS_EXECUTED',
    'FIELD_METHOD_CONFIDENCE_MULTIPLIERS',
    'FIELD_METHOD_THRESHOLDS',
    'FIELD_MUTATION_CONFIRMED',
    'FIELD_OPTIMIZED_DESCRIPTION',
    'FIELD_OPTIMIZED_KEYWORDS',
    'FIELD_POTENTIAL_FP',
    'FIELD_QUALITY_REASONS',
    'FIELD_RECOMMENDATIONS',
    'FIELD_REGRESSION_FAILED',
    'FIELD_ROLLBACK_RECOMMENDED',
    'FIELD_ROUTED_TO_FIXER',
    'FIELD_RULES_TRIGGERED',
    'FIELD_SAFETY_VERIFIER_USED',
    'FIELD_SIDE_EFFECTS_DETECTED',
    'FIELD_SIDE_EFFECT_SUMMARY',
    'FIELD_SUGGESTED_VALUE',
    'FIELD_SYNONYM_COVERAGE',
    'FIELD_THRESHOLD_ADJUST',
    'FIELD_TOTAL_BLINDSPOTS',
    'FIELD_TOTAL_FUNCTIONS',
    'FIELD_TOTAL_INPUT_FINDINGS',
    'FIELD_TRIGGER_EXAMPLES',
    'FINDING_KEY_ALIASES',
    'FINDING_KEY_SPEC',
    'FINDING_LIST_KEYS',
    'STRUCTURED_EXCLUDED_KEYS',
    'STRUCTURED_PRIORITY_KEYS',
    'FMT_DATETIME',
    'FMT_DATETIME_ISO',
    'FUNCTION_ORPHAN_BLINDSPOT_TYPES',
    'UNTESTED_COVERAGE_BLINDSPOT_TYPES',
    'FileRole',
    'GateDecision',
    'GateThresholds',
    'GuardLevel',
    'HARD_MAX_CLASS_LINES',
    'HARD_MAX_FILE_LINES',
    'HARD_MAX_FUNC_LINES',
    'HARD_MAX_METHOD_LINES',
    'HARD_MAX_NESTING',
    'HARD_MAX_PARAMS',
    'HASH_PREFIX_LEN',
    'HIGH_SEVERITY_PROTECTED',
    'INPLACE_MUTATING_METHODS',
    'HallucinationType',
    'HALLUCINATION_RULE_IDS',
    'FUNC_CLAIM_RE',
    'LINE_CLAIM_RE',
    'ORDINAL_FUNC_RE',
    'ORDINAL_LINE_RE',
    'ORDINAL_PASS_RE',
    'PASS_CLAIM_RE',
    'PASS_SUFFIX_CLAIM_RE',
    'THRESHOLD_PREFIX_OPS',
    'THRESHOLD_PREFIX_WORDS',
    'THRESHOLD_SUFFIX_WORDS',
    'HUMAN_CONFIRM_RULE_ID',
    'HALLUCINATION_NORMS',
    'NORM_INDEX',
    'NormCategory',
    'NormRule',
    'NormSeverity',
    'NormViolation',
    'SANDBOX_REFLECTION_FUNCS',
    'KEY_SEVERITIES',
    'LAYER_DEGRADE_EXC',
    'LAYER_DEGRADE_EXC_WITH_IMPORT',
    'LEGACY_TO_MAIN',
    'LEGACY_TO_SUB',
    'LINE_LIMIT',
    'MAX_CLASS_METHODS',
    'MAX_FILE_LINES',
    'MAX_FUNCTION_COMPLEXITY',
    'MAX_FUNCTION_LINES',
    'MAX_FUNC_LINES',
    'MAX_NESTING',
    'MAX_PARAMETERS',
    'MAX_SKILL_NAME_LENGTH',
    'MD_TABLE_SEP_3COL',
    'MESSAGE_TRUNCATE_LEN',
    'METHOD_DEGRADE_EXC',
    'MSG_CONFIRM_SKILL_DIR',
    'MSG_EXCEPTION_BROAD_HANDLER',
    'MSG_OSERROR_CONTINUE',
    'MSG_OSERROR_DEGRADED',
    'MSG_OSERROR_SUPPRESSED',
    'MSG_SYNTAX_ERROR_SKIP',
    'MSG_SYNTAX_ERROR_SKIP_DETECTION',
    'MSG_XV_VALIDATORS_IMPORT_FAIL',
    'MS_PER_SECOND',
    'MULTIPROCESSING_MODULE',
    'NEAR_BUDGET_RATIO',
    'NO_CODE_DETAIL',
    'NO_CODE_SCORE',
    'OUTPUT_TRUNCATE_LEN',
    'OperationType',
    'PARSE_DEGRADE_EXC',
    'PERCENT_FACTOR',
    'POLYMORPHIC_METHODS',
    'PREINTERVENTION_VERSION',
    'P_SCALE_LEVELS',
    'RESULT_STATUS_BUCKETS',
    'RETRO_SCORE_DIMENSIONS',
    'ROLE_HARD_THRESHOLDS',
    'ROLE_PATTERNS',
    'ROOT_SUBSYSTEM',
    'RULE_BROAD_EXCEPTION',
    'RULE_COMMAND_INJECTION',
    'RULE_CONNECTION_LEAK',
    'RULE_HARDCODED_CREDENTIAL',
    'RULE_HARDCODED_SECRET',
    'RULE_HIGH_COMPLEXITY',
    'RULE_ID_PREFIX_CATEGORY',
    'RULE_INSECURE_CONFIG',
    'RULE_MISSING_ANNOTATIONS',
    'RULE_MISSING_DOCSTRING',
    'RULE_MUTABLE_DEFAULT',
    'RULE_ORPHAN_FUNCTION',
    'RULE_PUBLIC_UNTESTED',
    'RULE_TOO_MANY_PARAMS',
    'RULE_TYPE_MAP',
    'RULE_UNREACHABLE_CODE',
    'RuleDesc',
    'SENSITIVE_NAME_KEYWORDS',
    'SEVERITY_BLOCKING',
    'SEVERITY_INFO',
    'SEVERITY_PENALTY_WEIGHTS',
    'SEVERITY_RANK',
    'SEVERITY_WARNING',
    'SHARED_BASE_CONSUMER_THRESHOLD',
    'SIGNAL_MUTATION_CONFIRMED_DEAD',
    'SIGNAL_MUTATION_VERIFIED',
    'SKILL_MD_LINE_LIMIT',
    'SKILL_NAME_MIN_LEN',
    'SOURCE_SEQUENCE_TYPES',
    'STAGE_METRICS_KEY_SPEC',
    'SUMMARY_STATUS_BUCKETS',
    'SUBPROCESS_CHECK_CALL',
    'SUBPROCESS_CHECK_OUTPUT',
    'SUB_ENGINE_META',
    'TAINT_LOCAL_TRUSTED_CATEGORIES',
    'TAINT_SOURCE_CATEGORY_BY_NAME',
    'Severity',
    'SizeGateStatus',
    'SplitStrategy',
    'TASK_BUDGETS',
    'TASK_BUDGET_FACTOR',
    'TRACEBACK_TRUNCATE_LEN',
    'WIRING_DECLARATION_ATTR',
    'TX_FAILED_STATUSES',
    'TX_FIXED_STATUSES',
    'TX_FP_CONFIRMED_STATUSES',
    'TX_ROLLED_BACK_STATUSES',
    'TYPE_ALL',
    'Thresholds',
    'VULN_DESERIALIZATION',
    'VULN_RENDER_TEMPLATE',
    'VULN_RENDER_TEMPLATE_STRING',
    'VulnerabilityCategory',
    'YAML_SAFE_LOADERS',
    'claim_number',
    'classify_fanout_level',
    'classify_fanout_role',
    'classify_file_role',
    'coerce_fanout_level',
    'coerce_fanout_role',
    'coerce_task_type',
    'describe_finding_keys',
    'describe_stage_metrics_keys',
    'diag_severity_to_p',
    'fanout_advisory_scope_text',
    'fanout_band_text',
    'fanout_degree_of',
    'fanout_level_is_mandatory',
    'fanout_level_label',
    'fanout_mandatory_scope_text',
    'fanout_threshold_of',
    'finalize_fanout_module_governance',
    'first_quantity_claim',
    'get_role_thresholds',
    'is_fanout_excluded_file',
    'is_finding_carrier_key',
    'is_threshold_context',
    'normalize_filepath',
    'register_check_provider',
    'register_review_provider',
    'registered_check_providers',
    'registered_review_providers',
    'resolve_fanout_degree',
    'resolve_fanout_governance_level',
]

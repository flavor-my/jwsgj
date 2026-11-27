from __future__ import annotations

import ast
import json
import logging
import os
import re
import threading
from collections import deque
from collections.abc import Callable, Iterable, Iterator, Mapping
from datetime import UTC, datetime
from enum import Enum
from functools import lru_cache, partial
from pathlib import Path
from typing import Any

from jwsgj.diag_detectors_registry import (
    _pattern_targets_literal_text,
    is_cli_entry_module_source,
    iter_heuristic_matches,
    iter_regex_matches,
    mask_non_code,
    pattern_matches_ast_heuristics,
)
from jwsgj.diag_detectors_registry import (
    get_registry as get_detector_registry,
)
from jwsgj.diag_guard_io import (
    atomic_write_text,
)
from jwsgj.diag_guard_state import (
    read_json_artifact,
)
from jwsgj.diag_shared_ast_nodes import is_mutable_default, resolve_import_binding
from jwsgj.diag_shared_ast_views import (
    call_head_is_shadowed,
    call_scope_map,
    collect_lexical_scope_table,
    parent_map,
    scope_import_tables,
    scope_shadows_import,
)
from jwsgj.diag_shared_source_core import (
    files_fingerprint,
    read_source_with_fingerprint,
)
from jwsgj.diag_types_normalize import (
    is_finite_num,
    severity_key,
    severity_literal_from_rank,
)
from jwsgj.diag_types_vocab import (
    PARSE_DEGRADE_EXC,
    SEVERITY_RANK,
    YAML_SAFE_LOADERS,
)
from jwsgj.log_config import log_swallowed
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    solidify_ssot_path,
)
from jwsgj.runtime_scope import (
    is_pruned_dirname,
    is_scan_py_name,
)

__all__ = [
    'AST_CHECKERS',
    'DEFAULT_SOLIDIFY_MODE',
    'RULES',
    'SolidificationRegistry',
    'SolidificationReport',
    'SolidificationRule',
    'SolidificationRuleGenerator',
    'SolidifyMode',
    'StaticSolidifier',
    'check_assert',
    'check_bare_except',
    'check_decorator_blind_line_span',
    'check_decorator_wraps',
    'check_derived_rule_id_literal_copy',
    'check_dual_projection_drift',
    'check_eval_exec',
    'check_except_as_e',
    'check_except_pass_governance',
    'check_format_injection',
    'check_inline_exemption_contains',
    'check_local_compact_timestamp',
    'check_local_complexity_branch_table',
    'check_main_guard_live_branch_copy',
    'check_missing_file_logged',
    'check_mutable_defaults',
    'check_named_arg_without_kwonly',
    'check_namespace_cartesian_shortfall',
    'check_pickle',
    'check_private_entry_contract_split',
    'check_requests_verify',
    'check_silent_except',
    'check_split_line_count',
    'check_subprocess_shell',
    'check_unordered_finding_truncation',
    'check_yaml_load',
    'collect_active_py_files',
    'delegated_sync_rule_ids',
    'invalidate_solidified_ssot',
    'load_solidified_ssot',
    'mask_non_code',
    'resolve_solidify_mode',
    'run_stage6d_solidify',
]
_log = logging.getLogger(__name__)
_LEVEL_DOMAIN = frozenset({1, 2, 3})
def _normalize_int(val: Any, default: int, context: str) -> int:
    if isinstance(val, bool):
        return default
    try:
        return int(val)
    except (TypeError, ValueError, OverflowError) as _e:
        log_swallowed(__name__, _e, context=f'{context}:{type(_e).__name__}')
        return default
def _normalize_level(val: Any, default: int = 1) -> int:
    n = _normalize_int(val, default, context='_normalize_level')
    return n if n in _LEVEL_DOMAIN else default
_PRIORITY_DOMAIN = frozenset({"P0", "P1", "P2", "P3"})
_DEFAULT_PRIORITY = "P1"
_DEFAULT_PATTERN_TYPE = "ast"
def _normalize_priority(val: Any, default: str = _DEFAULT_PRIORITY) -> str:
    if not isinstance(val, str):
        return default
    normalized = severity_key(val, default="")
    return normalized if normalized in _PRIORITY_DOMAIN else default
_SSOT_BOOL_VALUES = {
    **dict.fromkeys(("true", "1", "yes", "on"), True),
    **dict.fromkeys(("false", "0", "no", "off", ""), False),
}
def _normalize_bool(val: Any, default: bool) -> bool:
    if isinstance(val, bool):
        return val
    if isinstance(val, str):
        return _SSOT_BOOL_VALUES.get(val.strip().lower(), default)
    if isinstance(val, float) and not is_finite_num(val):
        return default
    if isinstance(val, (int, float)):
        return bool(val) if val in (0, 1) else default
    return default
def _normalize_str(val: Any, default: str = "") -> str:
    if isinstance(val, str):
        return val
    if val is None:
        return default
    return str(val)
def _normalize_id_text(value) -> str:
    return value.strip() if isinstance(value, str) else ""
_DETECTOR_IDENTIFIER_INVALID = re.compile(r"[^0-9A-Za-z_]")
def _detector_identifier(rule_id: str) -> str:
    ident = _DETECTOR_IDENTIFIER_INVALID.sub("_", str(rule_id))
    if not ident:
        return "unnamed"
    return "_" + ident if ident[0].isdigit() else ident
class SolidificationRule:
    __slots__ = (
        "auto_fix_enabled",
        "description",
        "enabled",
        "exempt_cli_entry",
        "fix_template",
        "has_l3_baseclass",
        "level",
        "match_code_only",
        "name",
        "pattern",
        "pattern_type",
        "priority",
        "rule_id",
        "source_skill",
    )
    def __init__(self, *, rule_id: str, name: str, level: int,
                 source_skill: str, pattern_type: str, pattern: str,
                 fix_template: str = "", description: str = "",
                 priority: str = _DEFAULT_PRIORITY, enabled: bool = True,
                 auto_fix_enabled: bool = False,
                 has_l3_baseclass: bool = False,
                 exempt_cli_entry: bool = False,
                 match_code_only: bool = False):
        self.rule_id = _normalize_str(rule_id).strip()
        self.name = _normalize_str(name)
        self.level = _normalize_level(level)
        self.source_skill = _normalize_str(source_skill)
        self.pattern_type = (
            _normalize_str(pattern_type, _DEFAULT_PATTERN_TYPE).strip().lower()
            or _DEFAULT_PATTERN_TYPE)
        self.pattern = _normalize_str(pattern)
        self.fix_template = _normalize_str(fix_template)
        self.description = _normalize_str(description)
        self.priority = _normalize_priority(priority)
        self.enabled = _normalize_bool(enabled, True)
        self.auto_fix_enabled = _normalize_bool(auto_fix_enabled, False)
        self.has_l3_baseclass = _normalize_bool(has_l3_baseclass, False)
        # 风格类规则（print→logger 等）对 CLI 入口模块不适用：入口模块的
        # stdout 就是交付面，改成 logger 会直接破坏 CLI 契约。
        self.exempt_cli_entry = _normalize_bool(exempt_cli_entry, False)
        # 正则规则若保留字符串内容做字面量判据，字符串/文档串里的同形文本
        # 不是可执行代码；match_code_only=True 只接受落在代码区的匹配。
        self.match_code_only = _normalize_bool(match_code_only, False)
    def to_dict(self) -> dict[str, Any]:
        return {s: getattr(self, s) for s in self.__slots__}
    @classmethod
    def from_ssot_row(cls, row: dict) -> SolidificationRule:
        return cls(
            rule_id=_normalize_id_text(row.get("rule_id")),
            name=_normalize_str(row.get("name")),
            level=row.get("level"),
            source_skill=_normalize_str(row.get("source_skill")),
            pattern_type=_normalize_str(row.get("pattern_type"),
                                        _DEFAULT_PATTERN_TYPE),
            pattern=_normalize_str(row.get("pattern")),
            fix_template=_normalize_str(row.get("fix_template")),
            description=_normalize_str(row.get("description")),
            priority=_normalize_priority(row.get("priority")),
            enabled=row.get("enabled"),
            auto_fix_enabled=row.get("auto_fix_enabled"),
            has_l3_baseclass=row.get("has_l3_baseclass"),
            exempt_cli_entry=row.get("exempt_cli_entry"),
            match_code_only=row.get("match_code_only"),
        )
    @classmethod
    def generated(cls, *, rule_id: str, source_rule: str, level: Any,
                  priority: Any, occurrence_count: Any,
                  source_skill: str = "",
                  detector_source: SolidificationRule | None = None,
                  ) -> SolidificationRule:
        count = _normalize_int(occurrence_count, 0,
                               context='SolidificationRule.generated')
        return cls(
            rule_id=rule_id,
            name=f"自动固化规则-{source_rule}",
            level=level,
            source_skill=source_skill or "",
            pattern_type=(detector_source.pattern_type
                          if detector_source is not None
                          else _DEFAULT_PATTERN_TYPE),
            pattern=detector_source.pattern if detector_source is not None else "",
            fix_template=(detector_source.fix_template
                          if detector_source is not None else ""),
            # 派生规则原样复用来源规则的正则，匹配范围语义必须一并继承。
            match_code_only=(detector_source.match_code_only
                             if detector_source is not None else False),
            # CLI 入口豁免同属匹配范围语义：不继承会让派生检测器在入口模块
            # 照报 print，而来源规则 CS-02 已整体豁免，同一规则两套结论。
            exempt_cli_entry=(detector_source.exempt_cli_entry
                              if detector_source is not None else False),
            description=(
                f"从诊断发现自动生成: 规则{source_rule}出现{count}次, "
                f"严重度{_normalize_priority(priority)}"
            ),
            priority=_normalize_priority(priority),
        )
_AI_FIX_NOTE = "（仅诊断，不改码；修复由 AI 审核并执行（经三层验证写盘））"
_builtin_rule = partial(
    SolidificationRule,
    level=1,
    source_skill="jwsgj",
)
RULES: list = [
    _builtin_rule(
        rule_id="CS-01", name="bare except → except Exception", pattern_type="ast",
        pattern="ExceptHandler with type=None",
        description="裸except会捕获所有异常包括SystemExit/KeyboardInterrupt" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-04", name="mutable default args", pattern_type="ast",
        pattern="FunctionDef with default=List/Dict/Set",
        description="可变默认参数在函数定义时只创建一次" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-23", name="assert in production", pattern_type="ast",
        pattern="Assert statement",
        description="assert在-O模式下被移除，生产代码不应依赖assert" + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-61", name="except missing as e", pattern_type="ast",
        pattern="ExceptHandler without name",
        fix_template="except Exception as e:",
        description="except无as e绑定导致无法记录异常信息",
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-64", name="decorator missing @wraps", pattern_type="ast",
        pattern="FunctionDef with decorator but no @wraps",
        fix_template="@functools.wraps(func)",
        description="装饰器缺@wraps导致被装饰函数丢失元信息",
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-05", name="silent except:pass", pattern_type="ast",
        pattern="ExceptHandler with body=[Pass]",
        description="except:pass静默吞掉异常，丢失错误信息" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-17", name="subprocess shell=True", pattern_type="ast",
        pattern="Call subprocess.call/Popen/run with shell=True",
        fix_template="shell=False",
        description="subprocess shell=True存在命令注入风险" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-18", name="eval/exec call", pattern_type="ast",
        pattern="Call Name eval/exec",
        description="eval/exec执行动态代码存在代码注入风险" + _AI_FIX_NOTE,
        priority="P0",
    ),
    _builtin_rule(
        rule_id="CS-20", name="pickle.loads unsafe", pattern_type="ast",
        pattern="Call pickle.loads",
        description="pickle.loads反序列化不可信数据可致任意代码执行" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-21", name="requests verify=False", pattern_type="ast",
        pattern="Call requests.get/post/put/delete with verify=False",
        fix_template="verify=True",
        description="requests verify=False跳过TLS证书校验存在中间人风险" + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-24", name="yaml.load unsafe", pattern_type="ast",
        pattern="Call yaml.load",
        fix_template="yaml.safe_load",
        description="yaml.load默认Loader可构造任意对象，应使用safe_load" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-76", name="non-literal .format() injection", pattern_type="ast",
        pattern="Call Attribute format on non-Constant",
        description="非字面量字符串调用.format()存在格式化注入风险" + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-89", name="except pass governance", pattern_type="ast",
        pattern="ExceptHandler with body=[Pass] (governance)",
        description="except仅pass的治理规则，与CS-05互补覆盖带类型异常静默" + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-02", name="print → logger", pattern_type="regex",
        # 排除两类「print 就是契约」的写法：①``[ok]/[warn]/…`` 协议前缀的
        # 面向用户消息；②``print(__doc__)`` 帮助输出。CLI 入口模块整体豁免
        # 走 ``exempt_cli_entry``。
        pattern=(r"\bprint\(\s*(?!f?[\"']\s*\["
                 r"(?:ok|warn|info|error|fail|debug)\])"
                 r"(?!__doc__)"),
        description="print输出到stdout不适合生产环境日志" + _AI_FIX_NOTE,
        priority="P2",
        exempt_cli_entry=True,
        # 模式含引号（\"[ok]\" 等负向前瞻）时词法层会保留字符串内容，
        # 若不再限定代码区，docstring/字符串里的 print( 会被当成调用。
        match_code_only=True,
    ),
    _builtin_rule(
        rule_id="CS-03", name="os.remove → safe_delete", pattern_type="regex",
        pattern=r"\bos\.remove\(|\bos\.rmdir\(|\bshutil\.rmtree\(",
        description="直接删除不可回滚，应使用安全删除函数" + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-65", name="star import", pattern_type="import",
        pattern="from X import *",
        fix_template="from X import name1, name2  # explicit imports",
        description="星号导入不导入_前缀名称且污染命名空间",
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-95", name="_log undefined → add import logging", pattern_type="call",
        pattern="_log. used but not imported",
        fix_template="import logging; _log = logging.getLogger(__name__)",
        description="_log变量未定义但被使用",
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-96", name="dead import removal", pattern_type="import",
        pattern="imported but never used",
        fix_template="# removed unused import",
        description="未使用的导入增加启动开销和循环依赖风险",
        priority="P3",
    ),
    _builtin_rule(
        rule_id="CS-98", name="missing __init__.py", pattern_type="other",
        pattern="directory without __init__.py",
        fix_template="# create empty __init__.py",
        description="缺__init__.py导致包导入失败",
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-99", name="豁免判定直接对整行做子串包含",
        pattern_type="ast",
        pattern="Compare exemption marker Constant in line Name",
        fix_template="cut = inline_comment_index(line_text)",
        description=(
            "字符串/文档串里的 nosec、noqa 会被整行子串命中，"
            "安全规则被数据静默关闭；须先定位注释段再判关键字"
        ) + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-100", name="行数统计用 split 尾换行多算一行",
        pattern_type="ast",
        pattern=r"len(Name.split('\n'))",
        fix_template="count_lines(source)  # 复用 SSOT",
        description=(
            "len(source.split(\"\\n\")) 在尾换行文件上多出空元素，"
            "硬限/告警线整体错位一格；行数一律走 SSOT count_lines()"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="FD-01", name="findings 截断前未按严重度排序",
        pattern_type="ast",
        pattern="Assign findings-like field with head-cut slice and no key= sort",
        fix_template="ordered = sorted(findings, key=_finding_order_key)",
        description=(
            "问题项列表在截断前没有按 severity/priority 排序，高危项会被"
            "低危项挤掉；排序与截断须共用同一 order key，并记录被截断数量"
        ) + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="FD-02", name="本地圈复杂度分支表", pattern_type="ast",
        pattern=(
            "isinstance branch-node tuple + unit increment without "
            "cyclomatic_complexity"
        ),
        fix_template="cyclomatic_complexity(node, iter_own_nodes)",
        description=(
            "模块已有共享圈复杂度原语，函数内仍维护本地分支节点表并自增计数，"
            "两套口径会随节点族更新而漂移（同一函数得出不同复杂度）"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="FD-03", name="作用域行区间漏算装饰器行", pattern_type="ast",
        pattern="Compare node.lineno <= line <= node.end_lineno",
        fix_template="start = definition_start_line(node)",
        description=(
            "装饰器行位于 FunctionDef/ClassDef.lineno 之前，直接用 lineno 判定"
            "归属会把装饰器行判到外层；作用域起点一律走 definition_start_line"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="FD-04", name="复制主入口活分支判定", pattern_type="ast",
        pattern="main_guard_branch(...) then select body/orelse locally",
        fix_template="live = main_guard_live_body(node)",
        description=(
            "已调用 main_guard_branch 取极性，又自行用 body/orelse 重算导入期"
            "活分支，遇到 __name__ in (...) 等静态不可判形态会单边走而丢边；"
            "活分支只保留 main_guard_live_body 一个实现"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="FD-05", name="具名实参校验未覆盖 kwonly", pattern_type="ast",
        pattern=(
            "keyword.arg membership check against args/posonlyargs only"
        ),
        fix_template="kwonly = _kwonly_param_names(node)",
        description=(
            "按名匹配实参时只收集 args/posonlyargs，漏掉 kwonly 形参，"
            "合法调用被判成非法（恒等递归/参数校验整体漏检）"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-101", name="命名空间×属性扩展表漏项",
        pattern_type="ast",
        pattern="dotted key table + namespace collection + attr collection",
        fix_template=(
            "{f'{ns}.{attr}': entry for ns in NAMESPACES for attr in ATTRS}"
        ),
        description=(
            "命名空间集合与属性名集合两份事实表都已存在，点号键表却只手抄了"
            "其中一个命名空间的组合；新增命名空间（如 __builtins__）会整族"
            "漏判，写盘红线/规则路由静默失效"
        ) + _AI_FIX_NOTE,
        priority="P1",
    ),
    _builtin_rule(
        rule_id="CS-102", name="本地重拼紧凑时间戳",
        pattern_type="ast",
        pattern="strftime('%Y%m%d%H%M%S') + millis zero-pad",
        fix_template="format_compact_ts(int(time.time() * 1000))",
        description=(
            "17 位紧凑时间戳已在 diag_types_normalize.format_compact_ts 定型，"
            "函数内再拼一遍 strftime + 毫秒补零会与 SSOT 各自演进（时区/取整/"
            "长度口径分叉），时间戳一律委托 canonical 入口"
        ) + _AI_FIX_NOTE,
        priority="P3",
    ),
    _builtin_rule(
        rule_id="CS-103", name="文件缺失正常态被并入异常留痕",
        pattern_type="ast",
        pattern="except FileNotFoundError: log_swallowed(...)",
        fix_template=(
            "if not path.is_file(): return None\n"
            "try: ...\nexcept FileNotFoundError: return None"
        ),
        description=(
            "首次写入前文件本就不存在，捕获 FileNotFoundError 后写 "
            "swallowed_exception 会向 WARNING+traceback 通道注入伪异常，"
            "污染日志驱动的退化检测；缺失是正常态，须先判存在性"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-104", name="派生规则 ID 元组被手抄为字面量",
        pattern_type="ast",
        pattern="rule-id values + identical rule-id literal tuple",
        fix_template="DERIVED = tuple(dict.fromkeys(RULE_IDS.values()))",
        description=(
            "规则 ID 表的取值需要去重派生时，另一处又手抄同一组规则 ID；"
            "新增/改名一个受管调用就会与派生值漂移（漏提、错提或旧 ID 残留）"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-105", name="同源数据双投影分叉",
        pattern_type="ast",
        pattern="local = _source(...) + hand-built constant-key dict",
        fix_template="return _project_fields(_source(...))",
        description=(
            "同一私有数据源，一处走统一投影函数、一处手拼常量键字典；"
            "空数据时手拼分支产出全 None 的伪证据，被下游当真值写进溯源"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
    _builtin_rule(
        rule_id="CS-106", name="私有副本与公开入口空值口径分叉",
        pattern_type="ast",
        pattern="def _helper -> None + sibling helper -> {} or {}",
        fix_template="return helper(...)  # 空值口径只保留一份",
        description=(
            "本模块的 _helper 与同目录兄弟模块的公开 helper 同名同形参，"
            "但空信封口径一个是 None、一个是 {}；消费方的 if not x / x.get() "
            "于是走哪份实现就两种结果，取不到数据时要么抛 AttributeError、"
            "要么静默当成「无发现」；检查范围只到空字典信封，列表/字符串的"
            "空值差异在真值判断上等价，不计入"
        ) + _AI_FIX_NOTE,
        priority="P2",
    ),
]
_BUILTIN_RULE_IDS = frozenset(rule.rule_id for rule in RULES)
def _rule_finding(rule, filepath, line: int, description: str = "",
                  match: str = "") -> dict:
    finding = {
        "rule_id": rule.rule_id,
        "rule_name": rule.name,
        "file": str(filepath),
        "line": line,
        "description": description or rule.description,
        "priority": rule.priority,
        "level": rule.level,
        "auto_fixable": rule.auto_fix_enabled,
    }
    if match:
        finding["match"] = match
    return finding
def _report(findings: list, rule, filepath, node, description: str) -> None:
    findings.append(_rule_finding(rule, filepath, node.lineno, description))
def _fix_directive(rule) -> str:
    return rule.fix_template or rule.description
def _iter_except_handlers(tree) -> Iterator[ast.ExceptHandler]:
    for node in walk_nodes(tree):
        if isinstance(node, ast.ExceptHandler):
            yield node
def _is_silent_except(handler: ast.ExceptHandler, *, bare: bool) -> bool:
    return ((handler.type is None) is bare
            and len(handler.body) == 1
            and isinstance(handler.body[0], ast.Pass))
def _mutable_default_params(node) -> list[str]:
    args = node.args
    positional = args.posonlyargs + args.args
    offset = len(positional) - len(args.defaults)
    names = [param.arg for index, param in enumerate(positional)
             if index >= offset
             and is_mutable_default(args.defaults[index - offset])]
    names.extend(param.arg
                 for param, default in zip(args.kwonlyargs, args.kw_defaults,
                                           strict=False)
                 if default is not None and is_mutable_default(default))
    return names
def check_mutable_defaults(tree, rule, findings, filepath) -> None:
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                                 ast.Lambda)):
            continue
        names = _mutable_default_params(node)
        if names:
            _report(findings, rule, filepath, node,
                    f"可变默认参数 {', '.join(names)} -> {_fix_directive(rule)}")
def check_assert(tree, rule, findings, filepath) -> None:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Assert):
            _report(findings, rule, filepath, node,
                    f"assert语句 -> {_fix_directive(rule)}")
def _decorator_chain_has_wraps(func_node) -> bool:
    for dec in func_node.decorator_list:
        expr = dec.func if isinstance(dec, ast.Call) else dec
        if isinstance(expr, ast.Attribute) and expr.attr == "wraps":
            return True
        if isinstance(expr, ast.Name) and expr.id == "wraps":
            return True
    return False
def _factory_param_names(func_node) -> set[str]:
    args = func_node.args
    names = {a.arg for a in args.args + args.posonlyargs + args.kwonlyargs}
    if args.vararg is not None:
        names.add(args.vararg.arg)
    if args.kwarg is not None:
        names.add(args.kwarg.arg)
    return names
def _inner_funcs_and_returns(func_node) -> tuple[list, set[str]]:
    inners: list = []
    returned: set[str] = set()
    stack = list(func_node.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            inners.append(node)
            continue
        if isinstance(node, (ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, ast.Return):
            if isinstance(node.value, ast.Name):
                returned.add(node.value.id)
            continue
        stack.extend(ast.iter_child_nodes(node))
    return inners, returned
def _calls_names_directly(func_node, names: set[str]) -> bool:
    stack = list(func_node.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda)):
            continue
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id in names):
            return True
        stack.extend(ast.iter_child_nodes(node))
    return False
def _is_wrapper_missing_wraps(child, factory_params: set[str],
                               returned_names: set[str]) -> bool:
    if child.name not in returned_names:
        return False
    if not _calls_names_directly(child, factory_params):
        return False
    return not _decorator_chain_has_wraps(child)
def _iter_missing_wraps(tree) -> Iterator[tuple]:
    reported: dict[int, tuple] = {}
    for node in walk_nodes(tree):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        params = _factory_param_names(node)
        if not params:
            continue
        inners, returned_names = _inner_funcs_and_returns(node)
        if not inners or not returned_names:
            continue
        for child in inners:
            if _is_wrapper_missing_wraps(child, params, returned_names):
                reported[id(child)] = (node, child)
    yield from reported.values()
def check_decorator_wraps(tree, rule, findings, filepath) -> None:
    for factory, wrapper in _iter_missing_wraps(tree):
        _report(findings, rule, filepath, wrapper,
                f"装饰器 {factory.name} 的内嵌 wrapper {wrapper.name} 缺少@wraps "
                f"-> {_fix_directive(rule)}")
def check_bare_except(tree, rule, findings, filepath) -> None:
    for node in _iter_except_handlers(tree):
        if node.type is None:
            _report(findings, rule, filepath, node,
                    f"裸except→固化建议: {_fix_directive(rule)}")
def check_silent_except(tree, rule, findings, filepath) -> None:
    for node in _iter_except_handlers(tree):
        if _is_silent_except(node, bare=True):
            _report(findings, rule, filepath, node,
                    f"except:pass→固化建议: {_fix_directive(rule)}")
def _except_type_display(exc_type: ast.AST) -> str:
    if isinstance(exc_type, ast.Name):
        return exc_type.id
    try:
        unparsed = ast.unparse(exc_type)
    except Exception as _e:  # noqa: BLE001 — unparse 失败回退
        log_swallowed(__name__, _e,
                      context=f'_except_type_display:{type(_e).__name__}')
        return "Exception"
    return unparsed or "Exception"
_AS_E_NAMES = frozenset({"e", "exc", "err", "error", "exception",
                              "ex", "excinfo"})

def _node_binds_name(node, name: str) -> bool:
    return bool(
        (isinstance(node, ast.Name) and node.id == name
         and not isinstance(node.ctx, ast.Load))
        # 形参（含嵌套 def/lambda 的参数）同样是绑定：嵌套函数自己声明了
        # 同名形参时，其体内读取不是未绑定异常对象，不能报“缺少 as e”。
        or (isinstance(node, ast.arg) and node.arg == name)
        # import 别名（``import x as e`` / ``from x import y as e``）同样在当前
        # 作用域绑定 name；无 asname 的 ``import a.b`` 只绑定顶层 ``a``。
        or (isinstance(node, ast.alias)
            and (node.asname or node.name.partition(".")[0]) == name)
        or (isinstance(node, ast.ExceptHandler) and node.name == name)
        or (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                              ast.ClassDef)) and node.name == name)
    )

def _handler_body_binds(body: list, name: str) -> bool:
    """handler 体内是否自己绑定了 name（赋值 / 嵌套 except / def / with ... as）。"""
    for stmt in body:
        for node in walk_nodes(stmt):
            if _node_binds_name(node, name):
                return True
    return False

def _handler_prior_binding(handler, name: str, load: ast.Name) -> bool:
    for node in _iter_own_scope_nodes(handler):
        if _node_precedes(node, load) and _node_binds_name(node, name):
            return True
    return False

def _handler_body_loads_as_e(handler) -> bool:
    """handler 体是否读取了未绑定的「异常对象惯用名」。

    只有这种才真是 ``except X:`` 缺 ``as e`` 导致的 NameError 风险。
    反过来，handler 体完全不引用异常对象时（典型：双模式导入回退
    ``except ImportError: from _shared import X``），强行补 ``as e`` 只会
    造出一个未使用变量（F841）——把风格建议当缺陷报，反过来逼出新的缺陷。
    当前执行域的直接读取只接受同域前序绑定；延迟作用域读取采用保守判定。
    """
    own_node_ids = {id(node) for node in _iter_own_scope_nodes(handler)}
    for node in walk_nodes(handler):
        if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)
                and node.id in _AS_E_NAMES):
            continue
        bound = (_handler_prior_binding(handler, node.id, node)
                 if id(node) in own_node_ids
                 else _handler_body_binds(handler.body, node.id))
        if not bound:
            return True
    return False

def check_except_as_e(tree, rule, findings, filepath) -> None:
    for node in _iter_except_handlers(tree):
        if node.type is None or node.name is not None:
            continue
        if not _handler_body_loads_as_e(node):
            continue
        exc_name = _except_type_display(node.type)
        _report(findings, rule, filepath, node,
                f"except {exc_name}缺少as e: 无法获取异常对象, {_fix_directive(rule)}")
def check_except_pass_governance(tree, rule, findings, filepath) -> None:
    for node in _iter_except_handlers(tree):
        if not _is_silent_except(node, bare=False):
            continue
        exc_type = _except_type_display(node.type)
        _report(findings, rule, filepath, node,
                f"固化建议({rule.name}): {rule.description} (except {exc_type} 只有pass)")
_SUBPROCESS_SHELL_APIS = frozenset({
    "run", "call", "check_call", "Popen", "check_output",
})
def _imported_module_matches(imported: str, module: str) -> bool:
    return imported == module or imported.split(".", maxsplit=1)[0] == module
def _iter_module_bound_calls(tree, module: str,
                             members: frozenset) -> Iterator[tuple]:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    for node in walk_nodes(tree):
        if not isinstance(node, ast.Call):
            continue
        if call_head_is_shadowed(node, lexical, scopes):
            continue
        func = node.func
        if isinstance(func, ast.Name):
            rec = resolve_import_binding(imports, parents, node, func.id)
            if (rec is not None and len(rec) == 3 and rec[0] == "from"
                    and _imported_module_matches(rec[1], module)
                    and rec[2] in members):
                yield node, rec[2]
        elif (isinstance(func, ast.Attribute)
              and isinstance(func.value, ast.Name)
              and func.attr in members):
            rec = resolve_import_binding(
                imports, parents, node, func.value.id)
            if (rec is not None and len(rec) == 2 and rec[0] == "import"
                    and _imported_module_matches(rec[1], module)):
                yield node, func.attr
def _constant_keyword_value(node: ast.Call,
                            keyword: str) -> ast.Constant | None:
    for kw in node.keywords:
        if kw.arg == keyword and isinstance(kw.value, ast.Constant):
            return kw.value
    return None
def check_subprocess_shell(tree, rule, findings, filepath) -> None:
    for node, _member in _iter_module_bound_calls(
            tree, "subprocess", _SUBPROCESS_SHELL_APIS):
        shell = _constant_keyword_value(node, "shell")
        if (shell is None and len(node.args) > 8
                and isinstance(node.args[8], ast.Constant)):
            shell = node.args[8]
        if shell is not None and bool(shell.value):
            _report(findings, rule, filepath, node,
                    f"subprocess shell=True→固化建议: {_fix_directive(rule)}")
_EVAL_EXEC_APIS = frozenset({"eval", "exec"})
def _non_builtin_eval_exec_call_ids(tree) -> frozenset[int]:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    excluded: set[int] = set()
    for node, _scope in lexical.calls:
        if not (isinstance(node.func, ast.Name)
                and node.func.id in _EVAL_EXEC_APIS):
            continue
        rec = resolve_import_binding(imports, parents, node, node.func.id)
        builtin_import = bool(
            rec is not None and len(rec) == 3
            and rec[0] == "from" and rec[1] == "builtins"
            and rec[2] in _EVAL_EXEC_APIS)
        if (call_head_is_shadowed(node, lexical, scopes)
                or (rec is not None and not builtin_import)):
            excluded.add(id(node))
    return frozenset(excluded)
def check_eval_exec(tree, rule, findings, filepath) -> None:
    shadowed_ids = _non_builtin_eval_exec_call_ids(tree)
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name)
                and node.func.id in _EVAL_EXEC_APIS
                and id(node) not in shadowed_ids):
            _report(findings, rule, filepath, node,
                    f"eval/exec调用→固化建议: {_fix_directive(rule)}")
    for node, _member in _iter_module_bound_calls(
            tree, "builtins", _EVAL_EXEC_APIS):
        _func = node.func
        if isinstance(_func, ast.Name) and _func.id in _EVAL_EXEC_APIS:
            continue
        _report(findings, rule, filepath, node,
                f"eval/exec调用→固化建议: {_fix_directive(rule)}")
_PICKLE_LOADS_APIS = frozenset({"loads"})
def check_pickle(tree, rule, findings, filepath) -> None:
    for node, _member in _iter_module_bound_calls(
            tree, "pickle", _PICKLE_LOADS_APIS):
        _report(findings, rule, filepath, node,
                f"不安全pickle→固化建议: {_fix_directive(rule)}")
_REQUESTS_VERIFY_APIS = frozenset({
    "request", "get", "head", "post", "put", "patch", "delete", "options",
})
def check_requests_verify(tree, rule, findings, filepath) -> None:
    for node, _member in _iter_module_bound_calls(
            tree, "requests", _REQUESTS_VERIFY_APIS):
        verify = _constant_keyword_value(node, "verify")
        if (verify is not None
                and verify.value is not None
                and not verify.value):
            _report(findings, rule, filepath, node,
                    f"requests verify=False→固化建议: {_fix_directive(rule)}")
_YAML_LOAD_APIS = frozenset({"load"})
def _yaml_load_loader_arg(node: ast.Call) -> ast.AST | None:
    for kw in node.keywords:
        if kw.arg == "Loader":
            return kw.value
    if len(node.args) >= 2:
        return node.args[1]
    return None
_YAML_SAFE_LOADER_MODULE_TAILS = frozenset({"loader", "cyaml"})
def _is_safe_yaml_loader(loader_node: ast.AST | None,
                         call_node: ast.Call, imports: dict, parents: dict,
                         lexical, scope) -> bool:
    if isinstance(loader_node, ast.Attribute):
        if loader_node.attr not in YAML_SAFE_LOADERS:
            return False
        owner = loader_node.value
        module_parts: list[str] = []
        while isinstance(owner, ast.Attribute):
            module_parts.append(owner.attr)
            owner = owner.value
        if not isinstance(owner, ast.Name):
            return False
        module_parts.reverse()
        root_name = owner.id
        if scope_shadows_import(lexical, scope, root_name):
            return False
        rec = resolve_import_binding(imports, parents, call_node, root_name)
        safe_module_path = (not module_parts or (
            len(module_parts) == 1
            and module_parts[0] in _YAML_SAFE_LOADER_MODULE_TAILS))
        if (rec is not None and len(rec) == 2 and rec[0] == "import"
                and _imported_module_matches(rec[1], "yaml")):
            return safe_module_path
        return bool(
            not module_parts and rec is not None and len(rec) == 3
            and rec[0] == "from" and _imported_module_matches(rec[1], "yaml")
            and rec[2] in _YAML_SAFE_LOADER_MODULE_TAILS)
    if isinstance(loader_node, ast.Name):
        if scope_shadows_import(lexical, scope, loader_node.id):
            return False
        rec = resolve_import_binding(
            imports, parents, call_node, loader_node.id)
        return bool(
            rec is not None and len(rec) == 3 and rec[0] == "from"
            and _imported_module_matches(rec[1], "yaml")
            and rec[2] in YAML_SAFE_LOADERS)
    return False
def check_yaml_load(tree, rule, findings, filepath) -> None:
    lexical = collect_lexical_scope_table(tree)
    scopes = call_scope_map(lexical)
    imports = scope_import_tables(tree)
    parents = parent_map(tree)
    for node, _member in _iter_module_bound_calls(
            tree, "yaml", _YAML_LOAD_APIS):
        if _is_safe_yaml_loader(
                _yaml_load_loader_arg(node), node, imports, parents,
                lexical, scopes.get(id(node))):
            continue
        _report(findings, rule, filepath, node,
                f"不安全yaml.load→固化建议: {_fix_directive(rule)}")
def check_format_injection(tree, rule, findings, filepath) -> None:
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "format"
                and not isinstance(node.func.value, ast.Constant)):
            _report(findings, rule, filepath, node,
                    f"非字面量字符串调用.format()存在注入风险: {_fix_directive(rule)}")
_INLINE_EXEMPTION_MARKER = re.compile(
    r"\b(?:noqa|nosec)\b|type:\s*ignore")
_INLINE_EXEMPTION_SUBJECTS = frozenset({
    "line", "line_text", "text", "src", "source", "source_line",
    "code_line", "raw_line",
})
def check_inline_exemption_contains(tree, rule, findings, filepath) -> None:
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], (ast.In, ast.NotIn))
                and len(node.comparators) == 1
                and isinstance(node.left, ast.Constant)
                and isinstance(node.left.value, str)
                and _INLINE_EXEMPTION_MARKER.search(node.left.value)
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id in _INLINE_EXEMPTION_SUBJECTS):
            continue
        _report(findings, rule, filepath, node,
                f"豁免标记直接对整行做子串包含: {_fix_directive(rule)}")
def check_split_line_count(tree, rule, findings, filepath) -> None:
    for node in walk_nodes(tree):
        if not (isinstance(node, ast.Call)
                and isinstance(node.func, ast.Name) and node.func.id == "len"
                and len(node.args) == 1 and not node.keywords):
            continue
        split_call = node.args[0]
        if not (isinstance(split_call, ast.Call)
                and isinstance(split_call.func, ast.Attribute)
                and split_call.func.attr == "split"
                and len(split_call.args) == 1 and not split_call.keywords
                and isinstance(split_call.args[0], ast.Constant)
                and split_call.args[0].value == "\n"):
            continue
        _report(findings, rule, filepath, node,
                f"split 尾换行导致行数多算: {_fix_directive(rule)}")
_FINDING_FIELD_NAMES = frozenset({
    "findings", "issues", "violations", "defects", "problems", "alerts",
})
_ORDERING_FUNCS = frozenset({"sorted", "nlargest", "nsmallest"})
_ORDER_PRESERVING_WRAPPERS = frozenset({"list", "tuple"})
_NON_SEVERITY_ORDER_KEYS = frozenset({
    "len", "str", "repr", "ascii", "bytes", "int", "float", "complex",
    "bool", "tuple", "list", "set", "frozenset", "dict", "ord", "hash",
    "bin", "hex", "oct",
})
_SPAN_HELPER_NAMES = frozenset({
    "definition_start_line", "own_scope_line_span", "_function_span",
})
_BRANCH_NODE_NAMES = frozenset({
    "If", "For", "AsyncFor", "While", "ExceptHandler", "IfExp", "BoolOp",
})
_DEF_NODE_TOKEN = re.compile(
    r"(?:FunctionDef|AsyncFunctionDef|ClassDef|Lambda)")
_KWONLY_TOKEN = re.compile(r"kwonly", re.IGNORECASE)
def _tail_name(node) -> str:
    while isinstance(node, ast.Subscript):
        node = node.value
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return node.attr
    return ""
def _call_name(node) -> str:
    if not isinstance(node, ast.Call):
        return ""
    func = node.func
    if isinstance(func, ast.Name):
        return func.id
    return func.attr if isinstance(func, ast.Attribute) else ""
def _enclosing_scope(node, parents):
    scope = parents.get(node)
    while scope is not None and not isinstance(
            scope, (ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda,
                    ast.ClassDef, ast.Module)):
        scope = parents.get(scope)
    return scope if scope is not None else node
def _iter_function_scopes(tree) -> Iterator:
    for node in walk_nodes(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            yield node
_SCOPE_BOUNDARY_NODES = (
    ast.FunctionDef, ast.AsyncFunctionDef, ast.Lambda, ast.ClassDef,
)
def _iter_own_scope_nodes(scope):
    pending = deque([scope])
    while pending:
        node = pending.popleft()
        if node is not scope and isinstance(node, _SCOPE_BOUNDARY_NODES):
            continue
        yield node
        pending.extend(ast.iter_child_nodes(node))
def _is_head_cut(subscript) -> bool:
    if not isinstance(subscript, ast.Subscript):
        return False
    cut = subscript.slice
    return (isinstance(cut, ast.Slice) and cut.upper is not None
            and (cut.lower is None
                 or (isinstance(cut.lower, ast.Constant)
                     and cut.lower.value == 0)))
def _node_precedes(node, other) -> bool:
    return ((getattr(node, "lineno", 0), getattr(node, "col_offset", 0))
            < (getattr(other, "lineno", 0), getattr(other, "col_offset", 0)))
def _is_within(node, ancestor, parents) -> bool:
    current = node
    while current is not None:
        if current is ancestor:
            return True
        current = parents.get(current)
    return False
def _same_order_target(target, ordered_value) -> bool:
    if (isinstance(target, (ast.Attribute, ast.Subscript))
            and isinstance(ordered_value, (ast.Attribute, ast.Subscript))):
        return ast.unparse(target) == ast.unparse(ordered_value)
    target_name = _tail_name(target)
    return bool(target_name) and target_name == _tail_name(ordered_value)
def _order_assignment_names(call, scope, parents,
                            ordered_value) -> set[str]:
    current = parents.get(call)
    while current is not None and current is not scope:
        names = {
            _tail_name(target)
            for target, value in _assign_value_pairs(current)
            if _is_within(call, value, parents)
            and _same_order_target(target, ordered_value)
        }
        names.discard("")
        if names:
            return names
        current = parents.get(current)
    return set()
def _has_usable_order_key(node) -> bool:
    key = next((kw.value for kw in node.keywords if kw.arg == "key"), None)
    if key is None:
        return False
    if _mentions_severity(key):
        return True
    if isinstance(key, ast.Lambda):
        return any(
            isinstance(child, (ast.Name, ast.Attribute))
            and "order" in (child.id if isinstance(child, ast.Name)
                            else child.attr).lower()
            for child in walk_nodes(key.body))
    if (isinstance(key, (ast.Name, ast.Attribute))
            and _tail_name(key) in _NON_SEVERITY_ORDER_KEYS):
        return False
    return not (
        isinstance(key, ast.Call)
        and _call_name(key) in {"itemgetter", "attrgetter"}
    )
def _has_severity_order(scope, cut, parents) -> bool:
    ordered_value = cut.value
    while (isinstance(ordered_value, ast.Call)
            and isinstance(ordered_value.func, ast.Name)
            and ordered_value.func.id in _ORDER_PRESERVING_WRAPPERS
            and len(ordered_value.args) == 1 and not ordered_value.keywords):
        ordered_value = ordered_value.args[0]
    cut_name = _tail_name(ordered_value)
    for node in walk_nodes(scope):
        if _enclosing_scope(node, parents) is not scope:
            continue
        if not isinstance(node, ast.Call) or not _has_usable_order_key(node):
            continue
        if _is_within(cut, node, parents):
            continue
        if ordered_value is not node and not _node_precedes(node, cut):
            continue
        name = _call_name(node)
        if name in _ORDERING_FUNCS:
            if ordered_value is node:
                return True
            if cut_name and cut_name in _order_assignment_names(
                    node, scope, parents, ordered_value):
                return True
        elif (name == "sort" and isinstance(node.func, ast.Attribute)
              and _same_order_target(node.func.value, ordered_value)):
            return True
    return False
def _assign_value_pairs(node):
    if isinstance(node, ast.Assign):
        for target in node.targets:
            yield target, node.value
    elif isinstance(node, ast.AnnAssign) and node.value is not None:
        yield node.target, node.value
_SEVERITY_TOKENS = ("severity", "priority")
def _mentions_severity(scope) -> bool:
    for node in walk_nodes(scope):
        if isinstance(node, ast.Name):
            token = node.id
        elif isinstance(node, ast.Attribute):
            token = node.attr
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
            token = node.value
        else:
            continue
        lowered = token.lower()
        if any(marker in lowered for marker in _SEVERITY_TOKENS):
            return True
    return False
def check_unordered_finding_truncation(tree, rule, findings, filepath) -> None:
    parents = parent_map(tree)
    for node in walk_nodes(tree):
        value_pairs = _assign_value_pairs(node)
        if isinstance(node, ast.Return) and node.value is not None:
            value_pairs = [*value_pairs, (node.value, node.value)]
        for target, value in value_pairs:
            if _tail_name(target) not in _FINDING_FIELD_NAMES:
                continue
            cuts = [child for child in walk_nodes(value)
                    if isinstance(child, ast.Subscript) and _is_head_cut(child)]
            if not cuts:
                continue
            scope = _enclosing_scope(node, parents)
            if not _mentions_severity(scope):
                continue
            if all(_has_severity_order(scope, cut, parents) for cut in cuts):
                continue
            _report(findings, rule, filepath, node,
                    f"截断问题项前未按严重度排序: {_fix_directive(rule)}")
def _branch_tuple_names(node) -> list[str]:
    if not isinstance(node, ast.Call) or _call_name(node) != "isinstance":
        return []
    if len(node.args) < 2:
        return []
    subject = node.args[1]
    members = subject.elts if isinstance(subject, ast.Tuple) else [subject]
    return [name for member in members
            if (name := _tail_name(member))]
def _has_unit_increment(scope) -> bool:
    for node in _iter_own_scope_nodes(scope):
        if (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)
                and isinstance(node.value, ast.Constant)
                and node.value.value == 1):
            return True
        if not (isinstance(node, ast.Assign)
                and isinstance(node.value, ast.BinOp)
                and isinstance(node.value.op, ast.Add)):
            continue
        left, right = node.value.left, node.value.right
        for target in node.targets:
            target_expr = ast.unparse(target)
            for unit, other in ((left, right), (right, left)):
                if (isinstance(unit, ast.Constant) and unit.value == 1
                        and ast.unparse(other) == target_expr):
                    return True
    return False
def _references_helper(tree, name: str) -> bool:
    for node in walk_nodes(tree):
        if isinstance(node, ast.Name) and node.id == name:
            return True
        if isinstance(node, ast.Attribute) and node.attr == name:
            return True
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            for alias in node.names:
                if (alias.asname or alias.name).split(".")[-1] == name:
                    return True
    return False
def check_local_complexity_branch_table(tree, rule, findings, filepath) -> None:
    if not _references_helper(tree, "cyclomatic_complexity"):
        return
    for func in _iter_function_scopes(tree):
        if any(isinstance(node, ast.Call)
               and _call_name(node) == "cyclomatic_complexity"
               for node in _iter_own_scope_nodes(func)):
            continue
        branch_kinds = {name for child in _iter_own_scope_nodes(func)
                        for name in _branch_tuple_names(child)
                        if name in _BRANCH_NODE_NAMES}
        if len(branch_kinds) < 2 or not _has_unit_increment(func):
            continue
        _report(findings, rule, filepath, func,
                f"本地圈复杂度分支表与共享原语重复: {_fix_directive(rule)}")
def _isinstance_def_names(scope) -> set[str]:
    names: set[str] = set()
    for node in _iter_own_scope_nodes(scope):
        if not isinstance(node, ast.Call) or _call_name(node) != "isinstance":
            continue
        if len(node.args) < 2:
            continue
        if not any(_DEF_NODE_TOKEN.search(name)
                   for name in _branch_tuple_names(node)):
            continue
        head = _tail_name(node.args[0])
        if head:
            names.add(head)
    return names
def check_decorator_blind_line_span(tree, rule, findings, filepath) -> None:
    for func in _iter_function_scopes(tree):
        if any(isinstance(node, ast.Call)
               and _call_name(node) in _SPAN_HELPER_NAMES
               for node in _iter_own_scope_nodes(func)):
            continue
        def_names = _isinstance_def_names(func)
        if not def_names:
            continue
        for child in _iter_own_scope_nodes(func):
            if not (isinstance(child, ast.Compare) and len(child.ops) == 2):
                continue
            middle = child.comparators[0]
            if (isinstance(middle, ast.Attribute)
                    and middle.attr == "lineno"):
                continue
            span_bases = {
                _tail_name(part.value) for part in walk_nodes(child)
                if isinstance(part, ast.Attribute)
                and part.attr in {"lineno", "end_lineno"}
            }
            if not (span_bases & def_names):
                continue
            _report(findings, rule, filepath, child,
                    f"作用域区间用裸行号漏算装饰器行: {_fix_directive(rule)}")
            break
def check_main_guard_live_branch_copy(tree, rule, findings, filepath) -> None:
    for func in _iter_function_scopes(tree):
        if func.name == "main_guard_live_body":
            continue
        calls_branch = any(isinstance(node, ast.Call)
                           and _call_name(node) == "main_guard_branch"
                           for node in _iter_own_scope_nodes(func))
        if not calls_branch:
            continue
        attrs = {child.attr for child in _iter_own_scope_nodes(func)
                 if isinstance(child, ast.Attribute)}
        if not {"body", "orelse"} <= attrs:
            continue
        _report(findings, rule, filepath, func,
                f"复制主入口活分支判定: {_fix_directive(rule)}")
_KEYWORD_ARG_OWNER = re.compile(
    r"(?:kw|kwarg|keyword)(?:_(?:arg|node))?$", re.IGNORECASE)
def _is_keyword_arg(node) -> bool:
    if not (isinstance(node, ast.Attribute) and node.attr == "arg"):
        return False
    return bool(_KEYWORD_ARG_OWNER.fullmatch(_tail_name(node.value)))
def _keyword_arg_derived_names(func) -> set[str]:
    def touches_keyword_arg(node) -> bool:
        return any(_is_keyword_arg(child) for child in walk_nodes(node))
    names: set[str] = set()
    for node in _iter_own_scope_nodes(func):
        if isinstance(node, ast.Assign) and touches_keyword_arg(node.value):
            names.update(target.id for target in node.targets
                         if isinstance(target, ast.Name))
    for node in _iter_own_scope_nodes(func):
        if not isinstance(node, (ast.For, ast.AsyncFor)):
            continue
        if not (touches_keyword_arg(node.iter)
                or (isinstance(node.iter, ast.Name)
                    and node.iter.id in names)):
            continue
        names.update(target.id for target in walk_nodes(node.target)
                     if isinstance(target, ast.Name))
    return names
def _touches_param_attr(node) -> bool:
    return any(isinstance(child, ast.Attribute)
               and child.attr in {"args", "posonlyargs"}
               for child in walk_nodes(node))
def _param_container_names(func) -> set[str]:
    names: set[str] = set()
    for node in _iter_own_scope_nodes(func):
        if isinstance(node, ast.Assign) and _touches_param_attr(node.value):
            names.update(target.id for target in node.targets
                         if isinstance(target, ast.Name))
    return names
def check_named_arg_without_kwonly(tree, rule, findings, filepath) -> None:
    for func in _iter_function_scopes(tree):
        if any(_KWONLY_TOKEN.search(token)
               for child in _iter_own_scope_nodes(func)
               for token in ((child.id,) if isinstance(child, ast.Name)
                             else ((child.attr,)
                                   if isinstance(child, ast.Attribute)
                                   else ()))):
            continue
        derived = _keyword_arg_derived_names(func)
        params = _param_container_names(func)
        reported = False
        for node in _iter_own_scope_nodes(func):
            if not (isinstance(node, ast.Compare) and len(node.ops) == 1
                    and isinstance(node.ops[0], (ast.In, ast.NotIn))):
                continue
            sides = [node.left, *node.comparators]
            keyword_side = any(_is_keyword_arg(side)
                               or (isinstance(side, ast.Name)
                                   and side.id in derived) for side in sides)
            param_side = any(
                (isinstance(side, ast.Name) and side.id in params)
                or _touches_param_attr(side) for side in sides)
            if not (keyword_side and param_side):
                continue
            _report(findings, rule, filepath, node,
                    f"具名实参校验未覆盖 kwonly 形参: {_fix_directive(rule)}")
            reported = True
            break
        if reported:
            continue
_EXISTENCE_GUARD_NAMES = frozenset({
    "isfile", "exists", "lexists", "isdir", "is_dir",
})
_PATH_READ_NAMES = frozenset({
    "read_text", "read_bytes", "readline", "readlines", "read",
})
_PATH_WRITE_MODE_FLAGS = frozenset("wax+")
_SWALLOW_LOG_NAME = "log_swallowed"
_COMPACT_TS_FORMAT = "%Y%m%d%H%M%S"
_MILLIS_DIRECTIVE = "03d"
_CANONICAL_TS_MODULE = "diag_types_normalize.py"
_CANONICAL_TS_HELPER = "format_compact_ts"
_RULE_ID_TOKEN = re.compile(r"^[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+$")
_RULE_REF_TOKEN = re.compile(r"^[A-Z][A-Z0-9]*-\d+$")
_IDENTIFIER_TOKEN = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
def _module_level_values(tree) -> Iterator[tuple[str, ast.expr]]:
    for node in tree.body:
        if (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)):
            yield node.targets[0].id, node.value
        elif (isinstance(node, ast.AnnAssign)
                and isinstance(node.target, ast.Name)
                and node.value is not None):
            yield node.target.id, node.value
def _module_str_collections(tree) -> dict[str, list[str]]:
    collections: dict[str, list[str]] = {}
    for name, value in _module_level_values(tree):
        if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name)
                and value.func.id in ("frozenset", "set", "tuple", "list")
                and len(value.args) == 1):
            value = value.args[0]
        if isinstance(value, (ast.Set, ast.Tuple, ast.List)):
            members = value.elts
        else:
            continue
        if len(members) >= 2 and all(
                isinstance(member, ast.Constant)
                and isinstance(member.value, str) for member in members):
            collections[name] = [member.value for member in members]
    return collections
def _dotted_key_pairs(table: ast.Dict) -> list[tuple[str, str]]:
    pairs: list[tuple[str, str]] = []
    for key in table.keys:
        if not (isinstance(key, ast.Constant) and isinstance(key.value, str)
                and key.value.count(".") == 1):
            continue
        namespace, attr = key.value.split(".")
        if _IDENTIFIER_TOKEN.match(namespace) and _IDENTIFIER_TOKEN.match(attr):
            pairs.append((namespace, attr))
    return pairs
def check_namespace_cartesian_shortfall(tree, rule, findings, filepath) -> None:
    collections = _module_str_collections(tree)
    for name, value in _module_level_values(tree):
        if not isinstance(value, ast.Dict):
            continue
        pairs = _dotted_key_pairs(value)
        if len(pairs) < 2:
            continue
        for attr_name, attrs in collections.items():
            attr_set = set(attrs)
            covered = [(ns, attr) for ns, attr in pairs if attr in attr_set]
            if len(covered) < 2 or {attr for _, attr in covered} != attr_set:
                continue
            covered_ns = {ns for ns, _ in covered}
            for ns_name, members in collections.items():
                if ns_name == attr_name or not set(members) > covered_ns:
                    continue
                missing = [
                    f"{namespace}.{attr}" for namespace in members
                    for attr in attrs
                    if attr not in {seen for ns, seen in covered
                                    if ns == namespace}]
                if not missing:
                    continue
                _report(findings, rule, filepath, value,
                        f"{name} 未按 {ns_name}×{attr_name} 展开 "
                        f"{missing[:6]}: {_fix_directive(rule)}")
def _millis_directive_present(node) -> bool:
    if isinstance(node, ast.FormattedValue) and node.format_spec is not None:
        spec = node.format_spec
        if isinstance(spec, ast.Constant):
            return _MILLIS_DIRECTIVE in str(spec.value)
        if isinstance(spec, ast.JoinedStr):
            return any(isinstance(part, ast.Constant)
                       and _MILLIS_DIRECTIVE in str(part.value)
                       for part in spec.values)
        return False
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and _MILLIS_DIRECTIVE in node.value)
def check_local_compact_timestamp(tree, rule, findings, filepath) -> None:
    if os.path.basename(str(filepath)) == _CANONICAL_TS_MODULE:
        return
    for func in _iter_function_scopes(tree):
        if any(isinstance(node, ast.Call)
               and _call_name(node) == _CANONICAL_TS_HELPER
               for node in _iter_own_scope_nodes(func)):
            continue
        has_format = has_millis = False
        for node in _iter_own_scope_nodes(func):
            if (isinstance(node, ast.Call) and _call_name(node) == "strftime"
                    and node.args
                    and isinstance(node.args[0], ast.Constant)
                    and isinstance(node.args[0].value, str)
                    and _COMPACT_TS_FORMAT in node.args[0].value):
                has_format = True
            has_millis = has_millis or _millis_directive_present(node)
        if has_format and has_millis:
            _report(findings, rule, filepath, func,
                    f"{func.name} 自拼紧凑时间戳: {_fix_directive(rule)}")
def _handler_type_names(handler) -> list[str]:
    node = handler.type
    if node is None:
        return []
    members = node.elts if isinstance(node, ast.Tuple) else [node]
    return [name for member in members
            if (name := getattr(member, "id", getattr(member, "attr", "")))]
def _is_path_read_call(node) -> bool:
    if not isinstance(node, ast.Call):
        return False
    name = _call_name(node)
    if name == "open":
        mode = node.args[1] if len(node.args) > 1 else None
        for keyword in node.keywords:
            if keyword.arg == "mode":
                mode = keyword.value
        if isinstance(mode, ast.Constant) and isinstance(mode.value, str):
            return not any(flag in mode.value
                           for flag in _PATH_WRITE_MODE_FLAGS)
        return True
    return name in _PATH_READ_NAMES
def _is_swallow_log_stmt(node) -> bool:
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and _call_name(node.value) == _SWALLOW_LOG_NAME)
def check_missing_file_logged(tree, rule, findings, filepath) -> None:
    for func in _iter_function_scopes(tree):
        if any(isinstance(node, ast.Call)
               and _call_name(node) in _EXISTENCE_GUARD_NAMES
               for node in _iter_own_scope_nodes(func)):
            continue
        for node in _iter_own_scope_nodes(func):
            if not isinstance(node, ast.Try):
                continue
            if not any(_is_path_read_call(child)
                       for child in _iter_own_scope_nodes(node)):
                continue
            for handler in node.handlers:
                if "FileNotFoundError" not in _handler_type_names(handler):
                    continue
                if not any(_is_swallow_log_stmt(child)
                           for child in _iter_own_scope_nodes(handler)):
                    continue
                rest = [stmt for stmt in handler.body
                        if not _is_swallow_log_stmt(stmt)]
                if not all(isinstance(stmt, (ast.Pass, ast.Return))
                           for stmt in rest):
                    continue
                _report(findings, rule, filepath, node,
                        f"{func.name} 缺失态被并入异常留痕: "
                        f"{_fix_directive(rule)}")
def _rule_id_strings(values) -> list[str] | None:
    strings = [item.value for item in values
               if isinstance(item, ast.Constant)
               and isinstance(item.value, str)]
    if len(strings) < 2 or len(strings) != len(values):
        return None
    if not all(_RULE_ID_TOKEN.match(text) or _RULE_REF_TOKEN.match(text)
               for text in strings):
        return None
    return strings
def check_derived_rule_id_literal_copy(tree, rule, findings,
                                       filepath) -> None:
    for name, value in _module_level_values(tree):
        if not isinstance(value, ast.Dict):
            continue
        strings = _rule_id_strings(value.values)
        if strings is None or len(set(strings)) == len(strings):
            continue
        expected = set(strings)
        for node in walk_nodes(tree):
            if node is value or not isinstance(
                    node, (ast.Tuple, ast.List, ast.Set)):
                continue
            copied = _rule_id_strings(node.elts)
            if copied is not None and set(copied) == expected:
                _report(findings, rule, filepath, node,
                        f"{name} 的取值被手抄为字面量: "
                        f"{_fix_directive(rule)}")
def _private_source_helpers(func) -> dict[str, str]:
    linked: dict[str, str] = {}
    for node in _iter_own_scope_nodes(func):
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1
                and isinstance(node.targets[0], ast.Name)
                and isinstance(node.value, ast.Call)):
            continue
        helper = _call_name(node.value)
        if helper.startswith("_"):
            linked[node.targets[0].id] = helper
    return linked
def check_dual_projection_drift(tree, rule, findings, filepath) -> None:
    delegated: dict[str, set[str]] = {}
    handrolled: dict[str, tuple] = {}
    for func in _iter_function_scopes(tree):
        linked = _private_source_helpers(func)
        for ret in _iter_own_scope_nodes(func):
            if not (isinstance(ret, ast.Return) and ret.value is not None):
                continue
            value = ret.value
            if isinstance(value, ast.Call):
                for child in walk_nodes(value):
                    helper = _call_name(child)
                    if isinstance(child, ast.Call) and helper.startswith("_"):
                        delegated.setdefault(func.name, set()).add(helper)
                continue
            if not (isinstance(value, ast.Dict) and len(value.keys) >= 2
                    and all(isinstance(key, ast.Constant)
                            for key in value.keys)):
                continue
            sources = {
                linked[item.func.value.id] for item in value.values
                if isinstance(item, ast.Call) and _call_name(item) == "get"
                and isinstance(item.func, ast.Attribute)
                and isinstance(item.func.value, ast.Name)
                and item.func.value.id in linked}
            if sources:
                handrolled[func.name] = (func, sources)
    for hand_name, (hand_node, sources) in handrolled.items():
        for delegate_name, helper_names in delegated.items():
            if delegate_name == hand_name:
                continue
            shared = sources & helper_names
            if not shared:
                continue
            _report(findings, rule, filepath, hand_node,
                    f"{hand_name} 手拼常量键字典与 {delegate_name} 的投影"
                    f"分叉(同源 {sorted(shared)}): {_fix_directive(rule)}")
def _sibling_source_snapshot(dirpath: str) -> tuple[tuple[str, ...], tuple]:
    try:
        names = os.listdir(dirpath)
    except OSError as exc:
        log_swallowed(__name__, exc, context="_sibling_source_snapshot")
        names = []
    paths = tuple(sorted(
        os.path.join(dirpath, name) for name in names if name.endswith(".py")))
    return paths, files_fingerprint(paths)
def _sibling_module_names(dirpath: str) -> frozenset[str]:
    paths, _fingerprint = _sibling_source_snapshot(dirpath)
    return frozenset(os.path.basename(path)[:-3] for path in paths)
@lru_cache(maxsize=128)
def _sibling_public_defs_cached(
        dirpath: str, paths: tuple[str, ...], fingerprint: tuple,
) -> dict[str, tuple]:
    del dirpath, fingerprint
    exports: dict[str, tuple] = {}
    for path in paths:
        module_name = os.path.basename(path)[:-3]
        try:
            with open(path, encoding="utf-8") as handle:
                sibling = ast.parse(handle.read())
        except (OSError, SyntaxError, UnicodeDecodeError, ValueError) as exc:
            log_swallowed(__name__, exc,
                          context=f"_sibling_public_defs:{module_name}")
            continue
        for node in sibling.body:
            if (isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and not node.name.startswith("_")):
                exports.setdefault(node.name, (module_name + ".py", node))
    return exports
def _sibling_public_defs(dirpath: str) -> dict[str, tuple]:
    paths, fingerprint = _sibling_source_snapshot(dirpath)
    return _sibling_public_defs_cached(dirpath, paths, fingerprint)
def _imported_module_tails(tree) -> set[str]:
    tails: set[str] = set()
    for node in walk_nodes(tree):
        if isinstance(node, ast.ImportFrom):
            if node.level > 1:
                continue
            if node.module:
                tails.add(node.module.split(".")[-1])
            elif node.level == 1:
                tails.update(alias.name for alias in node.names)
        elif isinstance(node, ast.Import):
            for alias in node.names:
                tails.add(alias.name.split(".")[-1])
    return tails
def _positional_param_names(func) -> list[str]:
    args = func.args
    return [arg.arg for arg in args.posonlyargs + args.args]
def _empty_value_kind(value) -> str:
    if value is None:
        return "none"
    if isinstance(value, ast.Constant):
        if value.value is None:
            return "none"
        return "str" if value.value == "" else ""
    if isinstance(value, ast.Dict):
        return "dict" if not value.keys else ""
    if isinstance(value, ast.List):
        return "list" if not value.elts else ""
    if isinstance(value, ast.Set):
        return "set" if not value.elts else ""
    return ""
def _iter_own_returns(func) -> Iterator[ast.Return]:
    stack = list(func.body)
    while stack:
        node = stack.pop()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef,
                             ast.Lambda, ast.ClassDef)):
            continue
        if isinstance(node, ast.Return):
            yield node
            continue
        stack.extend(ast.iter_child_nodes(node))
def _empty_return_kinds(func) -> set[str]:
    kinds: set[str] = set()
    for node in _iter_own_returns(func):
        value = node.value
        if isinstance(value, ast.BoolOp) and value.values:
            value = value.values[-1]
        elif isinstance(value, ast.IfExp):
            for branch in (value.body, value.orelse):
                kind = _empty_value_kind(branch)
                if kind:
                    kinds.add(kind)
            continue
        kind = _empty_value_kind(value)
        if kind:
            kinds.add(kind)
    return kinds
def check_private_entry_contract_split(tree, rule, findings,
                                       filepath) -> None:
    imported = _imported_module_tails(tree)
    if not imported:
        return
    directory = os.path.dirname(os.path.abspath(str(filepath)))
    if not imported & set(_sibling_module_names(directory)):
        return
    exports = _sibling_public_defs(directory)
    own_file = os.path.basename(str(filepath))
    for func in tree.body:
        if not isinstance(func, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        if not func.name.startswith("_") or func.name.startswith("__"):
            continue
        public_name = func.name[1:]
        entry = exports.get(public_name)
        if entry is None:
            continue
        owner, public = entry
        if owner == own_file or owner[:-3] not in imported:
            continue
        if _positional_param_names(func) != _positional_param_names(public):
            continue
        local_empty = _empty_return_kinds(func)
        public_empty = _empty_return_kinds(public)
        split = (("none" in local_empty and "dict" in public_empty)
                 or ("dict" in local_empty and "none" in public_empty))
        if not split:
            continue
        _report(findings, rule, filepath, func,
                f"{func.name} 与 {owner} 的 {public_name} 空值口径分叉"
                f"({sorted(local_empty)} vs {sorted(public_empty)}): "
                f"{_fix_directive(rule)}")
AST_CHECKERS: dict[str, Callable] = {
    "CS-01": check_bare_except,
    "CS-04": check_mutable_defaults,
    "CS-05": check_silent_except,
    "CS-17": check_subprocess_shell,
    "CS-18": check_eval_exec,
    "CS-20": check_pickle,
    "CS-21": check_requests_verify,
    "CS-23": check_assert,
    "CS-24": check_yaml_load,
    "CS-61": check_except_as_e,
    "CS-64": check_decorator_wraps,
    "CS-76": check_format_injection,
    "CS-89": check_except_pass_governance,
    "CS-99": check_inline_exemption_contains,
    "CS-100": check_split_line_count,
    "FD-01": check_unordered_finding_truncation,
    "FD-02": check_local_complexity_branch_table,
    "FD-03": check_decorator_blind_line_span,
    "FD-04": check_main_guard_live_branch_copy,
    "FD-05": check_named_arg_without_kwonly,
    "CS-101": check_namespace_cartesian_shortfall,
    "CS-102": check_local_compact_timestamp,
    "CS-103": check_missing_file_logged,
    "CS-104": check_derived_rule_id_literal_copy,
    "CS-105": check_dual_projection_drift,
    "CS-106": check_private_entry_contract_split,
}
def _read_ssot_rules(ssot_path) -> list | None:
    ssot_path = Path(ssot_path)
    if not ssot_path.exists():
        return []
    data, status, error = read_json_artifact(str(ssot_path))
    if status != "ok":
        _log.warning("SSOT读取失败(%s): %s", status, error)
        return None
    if not isinstance(data, dict):
        _log.warning("SSOT结构无效（顶层非对象）: %s", ssot_path)
        return None
    rules_data = data.get("rules", [])
    if not isinstance(rules_data, list):
        _log.warning("SSOT结构无效（rules 非列表）: %s", ssot_path)
        return None
    return rules_data
_SYNC_SKIP_IDS: frozenset[str] = frozenset({
    "CS-01", "CS-04", "CS-05", "CS-17", "CS-18",
    "CS-20", "CS-21", "CS-23", "CS-24",
    "CS-65", "CS-95", "CS-96", "CS-98",
})
def delegated_sync_rule_ids() -> frozenset[str]:
    """返回由其他子系统负责检测、不经 DetectorRegistry 同步的规则号。

    这批规则（裸except/可变默认参数/评估执行等）另有检测通道
    （build_preintervention / build_skill_health / build_refactor_collect），
    重复接线会让同一缺陷被报两次。漏报探针据此区分“能力缺失”与
    “职责已委派”，避免把正常的分工误判为漏报。
    """
    return _SYNC_SKIP_IDS
def _has_detection_semantics(rule: SolidificationRule) -> bool:
    if rule.pattern_type == "regex":
        if not rule.pattern:
            return False
        try:
            re.compile(rule.pattern)
        except (re.error, TypeError):
            return False
        return True
    if rule.pattern_type == "ast":
        return (rule.rule_id in AST_CHECKERS
                or pattern_matches_ast_heuristics(rule.pattern))
    return False
def _rule_has_live_semantics(rule) -> bool:
    return bool(rule.enabled) and _has_detection_semantics(rule)
def _try_sync_rule(det_registry, rule) -> bool:
    try:
        if rule.rule_id in _SYNC_SKIP_IDS:
            return False
        if not _rule_has_live_semantics(rule):
            unregister = getattr(det_registry, "unregister", None)
            if callable(unregister):
                unregister(rule.rule_id)
            if rule.enabled:
                _log.debug("规则 %s 尚无可执行检测语义，仅保留知识条目", rule.rule_id)
            return False
        det_registry.register_solidified_rule(
            rule_id=rule.rule_id,
            pattern_type=rule.pattern_type,
            pattern=rule.pattern,
            severity=rule.priority,
            # 豁免必须随规则一起下发到运行时检测器，否则静态固化路径放行、
            # 诊断路径照报（同一规则两套结论）。
            exempt_cli_entry=rule.exempt_cli_entry,
            code_only=rule.match_code_only,
        )
    except Exception as e:  # noqa: BLE001 — 单规则失败不得中断后续规则同步
        _log.warning("规则 %s 同步失败（跳过）: %s", rule.rule_id, e)
        return False
    return True
def _suggested_rule_id(suggestion: dict, source_rule: str) -> str:
    suggested_id = _normalize_id_text(suggestion.get("suggested_rule_id"))
    if suggested_id:
        return suggested_id
    return f"CS-GEN-{source_rule}" if source_rule else ""
def _overlay_ssot_row(existing: SolidificationRule, row: dict,
                      parsed: SolidificationRule) -> bool:
    changed = False
    for slot in SolidificationRule.__slots__:
        if slot == "rule_id" or slot not in row:
            continue
        if row[slot] is None:
            continue
        value = getattr(parsed, slot)
        if getattr(existing, slot) != value:
            setattr(existing, slot, value)
            changed = True
    return changed
def _merge_ssot_rows(existing: list, rows: list) -> int:
    loaded = 0
    by_id = {r.rule_id: r for r in existing}
    seen_row_ids: set[str] = set()
    for row in rows:
        if not isinstance(row, dict):
            continue
        parsed_row = SolidificationRule.from_ssot_row(row)
        if not parsed_row.rule_id:
            _log.warning("SSOT 行缺少可用 rule_id（%s），跳过装配",
                         type(row.get("rule_id")).__name__)
            continue
        if parsed_row.rule_id in seen_row_ids:
            _log.warning("SSOT 出现重复 rule_id(%s)，后者覆盖前者",
                         parsed_row.rule_id)
        seen_row_ids.add(parsed_row.rule_id)
        current = by_id.get(parsed_row.rule_id)
        if current is None:
            existing.append(parsed_row)
            by_id[parsed_row.rule_id] = parsed_row
            loaded += 1
        elif _overlay_ssot_row(current, row, parsed_row):
            loaded += 1
    return loaded
def _load_ssot_into_registry(registry: SolidificationRegistry,
                             yaml_path) -> int | None:
    try:
        yaml_path = Path(yaml_path)
        rules_data = _read_ssot_rules(yaml_path)
        if rules_data is None:
            return None
        loaded = _merge_ssot_rows(registry._rules, rules_data)
        _log.info("SSOT加载: 从%s加载%d条规则", yaml_path, loaded)
        return loaded
    except (OSError, json.JSONDecodeError, TypeError,
            UnicodeDecodeError, RecursionError) as e:
        _log.warning("SSOT加载失败: %s", e)
        return None
class SolidificationRegistry:
    def __init__(self) -> None:
        self._rules: list[SolidificationRule] = [
            SolidificationRule(**rule.to_dict()) for rule in RULES]
    def _index_of(self, rule_id: str) -> int | None:
        for i, rule in enumerate(self._rules):
            if rule.rule_id == rule_id:
                return i
        return None
    def list_rules(self, level: int | None = None) -> list[SolidificationRule]:
        if level is None:
            return list(self._rules)
        return [r for r in self._rules if r.level == level]
    def count(self) -> dict[str, int]:
        by_level = {level: 0 for level in sorted(_LEVEL_DOMAIN)}
        for rule in self._rules:
            if rule.level in by_level:
                by_level[rule.level] += 1
        return {
            "total": len(self._rules),
            **{f"level_{level}": n for level, n in by_level.items()},
        }
    def register(self, rule: SolidificationRule) -> None:
        if not rule.rule_id:
            _log.warning("拒绝注册：规则缺少可用 rule_id (%s)", rule.name)
            return
        idx = self._index_of(rule.rule_id)
        if idx is not None:
            self._rules[idx] = rule
            _log.info("更新固化规则: %s (%s)", rule.rule_id, rule.name)
            return
        self._rules.append(rule)
        _log.info("注册新固化规则: %s (%s)", rule.rule_id, rule.name)
    def register_from_suggestion(self, suggestion: dict,
                                 source_skill: str = "") -> SolidificationRule | None:
        if not isinstance(suggestion, dict):
            _log.warning("固化建议载荷非 dict（%s），拒绝注册",
                         type(suggestion).__name__)
            return None
        source_rule = _normalize_id_text(suggestion.get("source_rule"))
        suggested_id = _suggested_rule_id(suggestion, source_rule)
        if not suggested_id:
            _log.warning("固化建议缺少可用的规则标识，拒绝注册: %r", suggestion)
            return None
        if suggested_id == source_rule:
            _log.warning("派生规则 %s 不得覆盖同名来源规则，拒绝注册", suggested_id)
            return None
        if suggested_id in _BUILTIN_RULE_IDS:
            _log.warning("派生规则 %s 不得覆盖其他内置规则，拒绝注册", suggested_id)
            return None
        if source_rule.startswith("CS-GEN-"):
            _log.warning(
                "派生规则 %s 的来源 %s 已是派生规则，拒绝级联固化",
                suggested_id, source_rule)
            return None
        detector_source = self.find_by_rule_id(source_rule)
        rule = SolidificationRule.generated(
            rule_id=suggested_id,
            source_rule=source_rule,
            level=suggestion.get("suggested_level"),
            priority=suggestion.get("severity"),
            occurrence_count=suggestion.get("occurrence_count"),
            source_skill=source_skill,
            detector_source=detector_source,
        )
        self.register(rule)
        return rule
    def find_by_rule_id(self, rule_id: str) -> SolidificationRule | None:
        idx = self._index_of(rule_id)
        return self._rules[idx] if idx is not None else None
    def disable_unused_p3(self, findings_rule_ids: set[str]) -> list[str]:
        disabled: list[str] = []
        for rule in self._rules:
            if (rule.priority == "P3" and rule.rule_id not in findings_rule_ids
                    and rule.enabled):
                rule.enabled = False
                disabled.append(rule.rule_id)
        return disabled
    def load_from_yaml(self, yaml_path) -> int:
        loaded = _load_ssot_into_registry(self, yaml_path)
        return 0 if loaded is None else loaded
    def persist_to_yaml(self, yaml_path) -> bool:
        try:
            yaml_path = Path(yaml_path)
            yaml_path.parent.mkdir(parents=True, exist_ok=True)
            data = {
                "version": "1.0",
                "generated_at": datetime.now(UTC).isoformat(),
                "rules": [r.to_dict() for r in self._rules],
            }
            atomic_write_text(
                str(yaml_path),
                json.dumps(data, ensure_ascii=False, indent=2),
                tag="SolidifySSOT",
            )
            _log.info("SSOT持久化: %d条规则写入 %s", len(self._rules), yaml_path)
            return True
        except (OSError, TypeError, UnicodeEncodeError) as e:
            _log.warning("SSOT持久化失败: %s", e)
            return False
    def scope_rule_ids(self) -> frozenset[str]:
        return frozenset(
            rule.rule_id for rule in self._rules
            if rule.rule_id and rule.rule_id not in _SYNC_SKIP_IDS
            and _rule_has_live_semantics(rule))
    def sync_to_detector_registry(self) -> int:
        synced = 0
        try:
            det_registry = get_detector_registry()
            if not hasattr(det_registry, "register_solidified_rule"):
                _log.warning("检测器注册表不支持固化规则注册，同步跳过")
                return 0
            _install_authority(det_registry, self._rules)
            for rule in self._rules:
                if _try_sync_rule(det_registry, rule):
                    synced += 1
        except Exception as e:  # noqa: BLE001 — 同步失败仅 warning，不阻断固化主流程
            _log.warning("检测器注册表同步异常: %s", e)
        return synced
def _install_authority(det_registry, rules=None) -> int:
    rule_map = {r.rule_id: r for r in (RULES if rules is None else rules)}
    authority = {
        rid: (checker, rule_map[rid])
        for rid, checker in AST_CHECKERS.items()
        if rid in rule_map and rule_map[rid].enabled
    }
    try:
        return det_registry.install_solidified_authority(authority)
    except Exception as _e:  # noqa: BLE001 — 挂载失败软失败（权威路由退化兜底）
        log_swallowed(
            __name__, _e,
            context=f'install_solidified_authority:{type(_e).__name__}')
        return 0
def _py_str_literal(value: Any) -> str:
    return json.dumps(value if isinstance(value, str) else str(value),
                      ensure_ascii=False)
def _py_str_body(value: Any) -> str:
    return _py_str_literal(value)[1:-1]
def _gen_module_head(rule_id: str, rule_name: str, severity: str,
                     import_lines: tuple[str, ...] = (),
                     extra_consts: tuple[str, ...] = ()) -> list[str]:
    head = [
        '"""自动生成检测器: ' + _py_str_body(rule_id) + ' - '
        + _py_str_body(rule_name) + '"""',
    ]
    head.extend(import_lines)
    head.extend(['', 'RULE_ID = ' + _py_str_literal(rule_id)])
    head.extend(extra_consts)
    head.extend(['SEVERITY = ' + _py_str_literal(severity), ''])
    return head
def _gen_register_tail(safe_id: str) -> list[str]:
    return [
        '',
        'def register():',
        '    return (RULE_ID, detect_' + safe_id + ')',
    ]
_DETECTOR_AUTHORITY_MODULE = __name__
def _gen_authority_prefix(rule_id: str, rule_data: dict) -> list[str]:
    if rule_id not in AST_CHECKERS:
        return []
    return [
        '        # 权威路由: 委托同包 diag_solidify_rules.AST_CHECKERS 同名',
        '        # 权威检查器（单一权威源，判定与固化通道一致）',
        '        try:',
        '            import ' + _DETECTOR_AUTHORITY_MODULE + ' as _dsc',
        '            _checker = _dsc.AST_CHECKERS.get(RULE_ID)',
        '            _rule = _dsc.SolidificationRule(**' + repr(rule_data) + ')',
        '        except (ImportError, AttributeError):',
        '            _checker = None',
        '            _rule = None',
        '        if _checker is not None and _rule is not None:',
        '            _checker(tree, _rule, findings, file_path)',
        '            return findings',
    ]
def _gen_ast_detector_lines(rule_id: str, rule_name: str, pattern_desc: str,
                            safe_id: str, severity: str,
                            rule_data: dict) -> list[str]:
    return [
        *_gen_module_head(
            rule_id, rule_name, severity,
            import_lines=('import ast',),
            extra_consts=('PATTERN = ' + _py_str_literal(pattern_desc),)),
        'class Detector' + safe_id + ':',
        '    """检测器: ' + _py_str_body(rule_name) + '"""',
        '    rule_id = RULE_ID',
        '    severity = SEVERITY',
        '',
        '    def detect(self, tree, file_path=""):',
        '        findings = []',
        *_gen_authority_prefix(rule_id, rule_data),
        '        # 启发式判定复用 diag_detectors_registry 的唯一实现：',
        '        # 不在生成代码里再抄一份关键字副本（否则注册表扩展后漏检）。',
        '        from jwsgj.diag_detectors_registry import iter_heuristic_matches',
        '        for node in iter_heuristic_matches(tree, PATTERN):',
        '            findings.append({',
        '                "rule_id": RULE_ID,',
        '                "file": file_path,',
        '                "line": getattr(node, "lineno", 0),',
        '                "severity": SEVERITY,',
        '                "message": RULE_ID + ": " + PATTERN.lower()[:60],',
        '            })',
        '        return findings',
        '',
        'def detect_' + safe_id + '(source_code, file_path=""):',
        '    try:',
        '        compile(source_code, file_path or "<detect>", "exec")  # V1铁律',
        '        tree = ast.parse(source_code)',
        '        detector = Detector' + safe_id + '()',
        '        return detector.detect(tree, file_path)',
        '    except (SyntaxError, ValueError):',
        '        return []',
        *_gen_register_tail(safe_id),
    ]
def _gen_regex_detector_lines(rule_id: str, rule_name: str, pattern_desc: str,
                              safe_id: str, severity: str, *,
                              code_only: bool = False) -> list[str] | None:
    if not pattern_desc:
        _log.error("检测器代码生成失败: %s: 正则模式为空（无检测语义）", rule_id)
        return None
    try:
        re.compile(pattern_desc)
    except re.error as e:
        _log.error("检测器代码生成失败: %s: 正则表达式无效: %s", rule_id, e, exc_info=True)
        return None
    safe_pattern_repr = repr(pattern_desc)
    return [
        *_gen_module_head(rule_id, rule_name, severity,
                          extra_consts=('PATTERN = ' + safe_pattern_repr,)),
        'def detect_' + safe_id + '(source_code, file_path=""):',
        '    findings = []',
        '    from jwsgj.diag_detectors_registry import iter_regex_matches',
        ('    for i, raw, _match in iter_regex_matches(source_code, PATTERN,'
         ' code_only=True):' if code_only else
         '    for i, raw, _match in iter_regex_matches(source_code, PATTERN):'),
        '        findings.append({',
        '            "rule_id": RULE_ID,',
        '            "file": file_path,',
        '            "line": i,',
        '            "severity": SEVERITY,',
        '            "message": ' + _py_str_literal(rule_name + ': ')
        + ' + raw.strip()[:80],',
        '        })',
        '    return findings',
        *_gen_register_tail(safe_id),
    ]
def _finding_rule_id(f: dict) -> str:
    rid = f.get("rule_id")
    if isinstance(rid, str):
        return rid
    return str(rid) if rid else ""
def _finding_severity(f: dict) -> str:
    for field in ("priority", "severity"):
        normalized = severity_key(f.get(field))
        if normalized:
            return normalized
    return "P2"
def _iter_dict_findings(findings, context: str) -> Iterator[dict]:
    if isinstance(findings, Mapping):
        findings = [findings]
    elif isinstance(findings, (str, bytes, bytearray)):
        _log.warning("%s 载荷形态非法(%s)，按空处理",
                     context, type(findings).__name__)
        return
    elif findings is not None and not isinstance(findings, Iterable):
        _log.warning("%s 载荷非可迭代(%s)，按空处理",
                     context, type(findings).__name__)
        return
    for f in findings or ():
        if not isinstance(f, Mapping):
            _log.warning("%s 跳过非 dict 条目: %r", context, f)
            continue
        yield dict(f)
_MIN_OCCURRENCE_FOR_RULE = 3
_PATTERN_MINING_RULES: dict[str, str] = {
    r"\bexcept\s*:": "CS-GEN-bare-except",
    r"\bos\.remove\(": "CS-GEN-os-remove",
    r"\bprint\(": "CS-GEN-print",
}
def _group_findings_by_rule(diag_findings) -> dict[str, list[dict]]:
    by_rule: dict[str, list[dict]] = {}
    for f in _iter_dict_findings(
            diag_findings, "generate_from_diag 载荷"):
        by_rule.setdefault(str(f.get("rule_id") or "unknown"), []).append(f)
    return by_rule
def _build_rule_suggestion(rule_id: str, instances: list[dict]):
    rule_id = _normalize_id_text(rule_id)
    if (not rule_id or rule_id == "unknown"
            or rule_id.startswith("CS-GEN-")):
        return None
    _rank = min(
        (SEVERITY_RANK.get(_finding_severity(i), 99)
         for i in instances),
        default=99,
    )
    if _rank > 1 or len(instances) < _MIN_OCCURRENCE_FOR_RULE:
        return None
    return {
        "source_rule": rule_id,
        "occurrence_count": len(instances),
        "severity": severity_literal_from_rank(_rank),
        "suggested_level": 1,
        "suggested_rule_id": "CS-GEN-" + rule_id,
        "example_files": sorted({str(i.get("file") or "").strip()
                                 for i in instances} - {""})[:5],
    }
def _normalize_source_files(source_files) -> list:
    if not source_files:
        return []
    if isinstance(source_files, Mapping):
        _log.warning("固化扫描载荷不支持映射形态，按空处理")
        return []
    if isinstance(source_files, (str, bytes, os.PathLike)):
        candidates = [source_files]
    elif isinstance(source_files, Iterable):
        candidates = source_files
    else:
        _log.warning("固化扫描载荷非可迭代(%s)，按空处理",
                     type(source_files).__name__)
        return []
    normalized: list = []
    for item in candidates:
        if not isinstance(item, (str, bytes, os.PathLike)):
            _log.warning("固化扫描跳过非路径条目: %r", item)
            continue
        path_text = os.fsdecode(os.fspath(item)).strip()
        if path_text:
            normalized.append(path_text)
    return normalized
class SolidificationRuleGenerator:
    def generate_from_diag(self, diag_findings: Any) -> Any:
        suggestions = []
        if not diag_findings:
            return suggestions
        for rule_id, instances in _group_findings_by_rule(diag_findings).items():
            suggestion = _build_rule_suggestion(rule_id, instances)
            if suggestion is not None:
                suggestions.append(suggestion)
        return suggestions
    def generate_from_pattern(self, source_files: Any) -> Any:
        findings = []
        source_files = _normalize_source_files(source_files)
        if not source_files:
            return findings
        for filepath in source_files:
            source, _fp = read_source_with_fingerprint(str(filepath))
            if source is None:
                _log.warning("源文件读取失败，跳过: %s", filepath)
                continue
            subjects: dict[bool, str | None] = {}
            for pattern, suggested_rule in _PATTERN_MINING_RULES.items():
                subject = _regex_subject(source, pattern, subjects)
                if subject is None:
                    _log.debug("模式挖掘: 源码投影不可用，跳过 %s", filepath)
                    break
                matches = re.findall(pattern, subject)
                if matches:
                    findings.append({
                        "rule_id": suggested_rule,
                        "file": str(filepath),
                        "count": len(matches),
                        "pattern": pattern,
                    })
        return findings
    def solidify_from_diag(
        self,
        diag_findings: list[dict],
        registry: SolidificationRegistry | None = None,
        source_skill: str = "",
    ) -> list[SolidificationRule]:
        suggestions = self.generate_from_diag(diag_findings)
        if registry is None:
            registry = SolidificationRegistry()
        new_rules: list[SolidificationRule] = []
        for sug in suggestions:
            rule = registry.register_from_suggestion(
                sug, source_skill=source_skill)
            if rule:
                new_rules.append(rule)
                _log.info(
                    "知识固化: 规则%s → %s (出现%d次, 严重度%s)",
                    sug.get("source_rule", ""),
                    rule.rule_id,
                    sug.get("occurrence_count", 0),
                    sug.get("severity", ""),
                )
        return new_rules
    def generate_detector_code(self, rule):
        rule_id = rule.rule_id
        rule_name = rule.name
        pattern_type = rule.pattern_type
        pattern_desc = str(rule.pattern or "")
        safe_id = _detector_identifier(rule_id)
        severity = rule.priority
        if not _has_detection_semantics(rule):
            _log.debug("规则 %s 无可执行检测语义（知识条目），不生成检测器", rule_id)
            return ""
        if pattern_type == "ast":
            if (rule_id not in AST_CHECKERS
                    and not pattern_matches_ast_heuristics(pattern_desc)):
                _log.warning(
                    "规则 %s 的 AST 模式无已知启发式语义，跳过检测器生成",
                    rule_id)
                return ""
            lines = _gen_ast_detector_lines(
                rule_id, rule_name, pattern_desc, safe_id, severity,
                rule.to_dict())
        elif pattern_type == "regex":
            lines = _gen_regex_detector_lines(
                rule_id, rule_name, pattern_desc, safe_id, severity,
                code_only=rule.match_code_only)
            if lines is None:
                return ""
        else:
            _log.warning(
                "规则 %s 的 pattern_type=%s 无生成器，跳过检测器代码生成",
                rule_id, pattern_type)
            return ""
        detector_code = "\n".join(lines) + "\n"
        try:
            compile(detector_code, "<generated_" + rule_id + ">", "exec")
            _log.info("检测器代码生成成功: %s (可编译)", rule_id)
        except (SyntaxError, ValueError) as e:
            _log.error("检测器代码生成失败: %s: %s", rule_id, e, exc_info=True)
            return ""
        return detector_code
    def solidify_and_generate(self, diag_findings, registry=None, skill_dir=None):
        if registry is None:
            registry = SolidificationRegistry()
        target_root = str(skill_dir).strip() if skill_dir else ""
        source_skill = (os.path.basename(os.path.normpath(target_root))
                        if target_root else "")
        existing_ids = {rule.rule_id for rule in registry.list_rules()}
        new_rules = self.solidify_from_diag(
            diag_findings, registry, source_skill=source_skill)
        if not new_rules:
            return {
                "rules_created": 0,
                "detectors_generated": 0,
                "ssot_persisted": False,
                "detectors_synced": 0,
            }
        if target_root:
            ssot_path = Path(solidify_ssot_path(target_root))
            ssot_persisted = registry.persist_to_yaml(ssot_path)
            if ssot_persisted:
                synced = registry.sync_to_detector_registry()
                expected_synced = len(registry.scope_rule_ids())
                if synced == expected_synced:
                    _bind_registry_scope(
                        _solidify_loaded_key(target_root), registry)
                else:
                    invalidate_solidified_ssot(target_root)
                    _log.warning(
                        "检测器同步不完整(%d/%d)：保留加载缓存失效状态，"
                        "不切换规则作用域", synced, expected_synced)
            else:
                synced = 0
                _log.warning("SSOT持久化失败：不同步检测器，也不切换规则作用域")
        else:
            ssot_persisted = False
            synced = 0
            _log.warning(
                "知识固化未提供目标项目根：仅保留内存规则，跳过持久化与检测器同步")
        return {
            "rules_created": sum(
                1 for rule in new_rules if rule.rule_id not in existing_ids),
            "detectors_generated": sum(
                1 for rule in new_rules if self.generate_detector_code(rule)),
            "ssot_persisted": ssot_persisted,
            "detectors_synced": synced,
        }
_QMON_DISABLE_QUALITY = 50.0
class SolidificationReport:
    _EMPTY_REPORT_TEXT = "# 代码固化报告\n\n**结果**: 未发现待固化点\n"
    @staticmethod
    def generate(findings: list[dict], output_path: Path | None = None,
                 registry: SolidificationRegistry | None = None) -> str:
        findings = list(_iter_dict_findings(findings, "报告载荷"))
        if not findings:
            return SolidificationReport._gen_write_report(
                SolidificationReport._EMPTY_REPORT_TEXT, output_path)
        if registry is None:
            registry = SolidificationRegistry()
        lines = SolidificationReport._gen_build_header(findings)
        lines.extend(SolidificationReport._gen_build_priority(findings, registry))
        lines.extend(SolidificationReport._gen_build_type(findings, registry))
        lines.extend(SolidificationReport._gen_build_details(findings, registry))
        report = "\n".join(lines)
        return SolidificationReport._gen_write_report(report, output_path)
    @staticmethod
    def _gen_build_header(findings: list[dict]) -> list[str]:
        return [
            "# 代码固化报告",
            "",
            f"**生成时间**: {datetime.now(UTC).isoformat()}",
            f"**待固化点**: {len(findings)} 个",
            "",
        ]
    @staticmethod
    def _resolved_priority(
        finding: dict, registry: SolidificationRegistry,
    ) -> tuple[Any, str]:
        rule = registry.find_by_rule_id(_finding_rule_id(finding))
        return rule, (rule.priority if rule else _finding_severity(finding))
    @staticmethod
    def _resolved_auto_fixable(finding: dict, rule: Any) -> bool:
        if rule is not None:
            return bool(rule.auto_fix_enabled)
        return _normalize_bool(finding.get("auto_fixable"), False)
    @staticmethod
    def _gen_build_priority(findings: list[dict], registry: SolidificationRegistry) -> list[str]:
        priority_counts: dict[str, int] = {}
        auto_fixable = 0
        for f in findings:
            rule, prio = SolidificationReport._resolved_priority(f, registry)
            priority_counts[prio] = priority_counts.get(prio, 0) + 1
            if SolidificationReport._resolved_auto_fixable(f, rule):
                auto_fixable += 1
        result = ["## 按优先级统计", ""]
        for pri in ["P0", "P1", "P2", "P3"]:
            if priority_counts.get(pri):
                result.append(f"- **{pri}**: {priority_counts[pri]} 个")
        if auto_fixable:
            result.append(f"- **可自动修复**: {auto_fixable} 个")
        return result
    @staticmethod
    def _gen_build_type(findings: list[dict], registry: SolidificationRegistry) -> list[str]:
        type_counts: dict[str, int] = {}
        name_by_rule: dict[str, str] = {}
        for f in findings:
            t = _finding_rule_id(f) or "unknown"
            type_counts[t] = type_counts.get(t, 0) + 1
            if t not in name_by_rule and f.get("rule_name"):
                name_by_rule[t] = f.get("rule_name", "")
        result = ["", "## 按类型统计", ""]
        for t, c in sorted(type_counts.items(), key=lambda kv: (-kv[1], kv[0])):
            rule = registry.find_by_rule_id(t)
            rule_name = rule.name if rule else name_by_rule.get(t, "")
            result.append(f"- **{t}** ({rule_name}): {c} 个")
        return result
    @staticmethod
    def _gen_build_detail(index: int, finding: dict,
                          registry: SolidificationRegistry) -> list[str]:
        rid = _finding_rule_id(finding)
        rule, prio = SolidificationReport._resolved_priority(finding, registry)
        auto_tag = (" [自修复]"
                    if SolidificationReport._resolved_auto_fixable(finding, rule)
                    else "")
        detail = _normalize_str(finding.get("description")).strip()
        hit = _normalize_str(finding.get("match")).strip()
        desc = detail or (rule.description if rule else "")
        line_no = finding.get("line")
        line_text = "" if line_no is None else line_no
        lines = [
            f"### {index}. [{prio}] {rid}{auto_tag}",
            f"- **文件**: `{finding.get('file') or ''}`",
            f"- **行号**: {line_text}",
            f"- **描述**: {desc}",
        ]
        if hit and hit != detail:
            lines.append(f"- **命中**: `{hit}`")
        lines.append("")
        return lines
    @staticmethod
    def _gen_build_details(findings: list[dict], registry: SolidificationRegistry) -> list[str]:
        result = ["", "## 详细清单", ""]
        for index, finding in enumerate(findings, 1):
            result.extend(SolidificationReport._gen_build_detail(
                index, finding, registry))
        return result
    @staticmethod
    def _gen_write_report(report: str, output_path: Path | None) -> str:
        if not output_path:
            return report
        if not isinstance(output_path, (str, os.PathLike)):
            _log.warning("固化报告落点非路径(%s)，仅返回文本",
                         type(output_path).__name__)
            return report
        try:
            atomic_write_text(os.fsdecode(os.fspath(output_path)), report,
                              tag="SolidifyReport")
        except (OSError, UnicodeEncodeError, TypeError) as e:
            _log.warning("固化报告写盘失败(%s): %s，返回文本不阻断", output_path, e)
        return report
    @staticmethod
    def _qmon_coverage(findings: list[dict],
                       registered_ids: set[str]) -> tuple[int, int, dict[str, int]]:
        covered = 0
        uncovered_by_severity: dict[str, int] = {}
        for f in findings:
            rid = _finding_rule_id(f)
            if rid in registered_ids:
                covered += 1
                continue
            sev = _finding_severity(f)
            uncovered_by_severity[sev] = uncovered_by_severity.get(sev, 0) + 1
        return covered, len(findings) - covered, uncovered_by_severity
    @staticmethod
    def _qmon_rule_stats(all_rules: list) -> tuple[dict[str, int], int]:
        type_dist: dict[str, int] = {}
        auto_fixable = 0
        for r in all_rules:
            type_dist[r.pattern_type] = type_dist.get(r.pattern_type, 0) + 1
            if r.auto_fix_enabled:
                auto_fixable += 1
        return type_dist, auto_fixable
    @staticmethod
    def _qmon_quality_score(p0_uncovered: int, p1_uncovered: int,
                            coverage_rate: float, auto_fix_rate: float) -> float:
        score = 100.0
        score -= p0_uncovered * 20
        score -= p1_uncovered * 10
        score -= max(0, (1.0 - coverage_rate) * 30)
        score -= max(0, (1.0 - auto_fix_rate) * 20)
        return max(0, min(100, score))
    @staticmethod
    def _qmon_disable_unused_p3(
        findings: list[dict], quality_score: float,
        registry: SolidificationRegistry,
    ) -> list[str]:
        if quality_score >= _QMON_DISABLE_QUALITY:
            return []
        findings_rule_ids = {_finding_rule_id(f) for f in findings}
        disabled = registry.disable_unused_p3(findings_rule_ids)
        _log.warning("质量监控: 禁用%d个低覆盖P3规则(质量分<%.0f)",
                     len(disabled), _QMON_DISABLE_QUALITY)
        return disabled
    @staticmethod
    def batch_quality_monitor(
        findings: list[dict],
        registry: SolidificationRegistry | None = None,
    ) -> dict[str, Any]:
        if registry is None:
            registry = SolidificationRegistry()
        findings = list(_iter_dict_findings(findings, "报告载荷"))
        all_rules = registry.list_rules()
        registered_ids = {r.rule_id for r in all_rules if r.enabled}
        total_findings = len(findings)
        covered, uncovered, uncovered_by_severity = (
            SolidificationReport._qmon_coverage(findings, registered_ids))
        type_dist, auto_fixable = SolidificationReport._qmon_rule_stats(all_rules)
        coverage_rate = covered / total_findings if total_findings > 0 else 1.0
        auto_fix_rate = auto_fixable / len(all_rules) if all_rules else 0.0
        p0_uncovered = uncovered_by_severity.get("P0", 0)
        p1_uncovered = uncovered_by_severity.get("P1", 0)
        quality_score = SolidificationReport._qmon_quality_score(
            p0_uncovered, p1_uncovered, coverage_rate, auto_fix_rate)
        disabled_rules = SolidificationReport._qmon_disable_unused_p3(
            findings, quality_score, registry)
        return {
            "total_findings": total_findings,
            "covered": covered,
            "uncovered": uncovered,
            "coverage_rate": round(coverage_rate, 4),
            "uncovered_by_severity": uncovered_by_severity,
            "p0_uncovered": p0_uncovered,
            "p1_uncovered": p1_uncovered,
            "total_rules": len(all_rules),
            "auto_fixable_rules": auto_fixable,
            "auto_fix_rate": round(auto_fix_rate, 4),
            "type_distribution": type_dist,
            "quality_score": round(quality_score, 1),
            "quality_grade": ("A" if quality_score >= 90
                              else "B" if quality_score >= 70
                              else "C" if quality_score >= 50 else "D"),
            "disabled_rules": disabled_rules,
            "rules_adjusted": len(disabled_rules),
        }
class SolidifyMode(Enum):
    PATTERN = 'pattern'
    RULE = 'rule'
    FIX = 'fix'
    KNOWLEDGE = 'knowledge'
    FULL = 'full'
DEFAULT_SOLIDIFY_MODE = SolidifyMode.FULL
_MODE_RULE_TYPES: dict[SolidifyMode, frozenset[str] | None] = {
    SolidifyMode.FULL: None,
    SolidifyMode.RULE: frozenset({"ast"}),
    SolidifyMode.PATTERN: frozenset({"regex"}),
    SolidifyMode.FIX: frozenset({"ast", "regex"}),
    SolidifyMode.KNOWLEDGE: frozenset({"ast", "regex"}),
}
def collect_active_py_files(root: str | os.PathLike) -> list[Path]:
    root_text = ""
    if isinstance(root, (str, bytes, os.PathLike)):
        root_text = os.fsdecode(os.fspath(root)).strip()
    if not root_text:
        _log.debug("collect_active_py_files: 空根入参，返回空集")
        return []
    root_path = Path(root_text)
    if not root_path.is_dir():
        return []
    active: list[Path] = []
    for py in sorted(root_path.rglob("*")):
        if not py.is_file() or not is_scan_py_name(py.name):
            continue
        try:
            rel_parts = py.relative_to(root_path).parts
        except ValueError as _e:  # pragma: no cover - 防御：rglob 产物恒在 root 下
            log_swallowed(
                __name__, _e,
                context=f'collect_active_py_files:{type(_e).__name__}')
            continue
        dir_segs = rel_parts[:-1]
        if any(is_pruned_dirname(seg, prune_tests=True) for seg in dir_segs):
            continue
        active.append(py)
    return active
def _regex_subject(source: str, pattern: str,
                   cache: dict[bool, str | None]) -> str | None:
    keep_strings = _pattern_targets_literal_text(pattern)
    if keep_strings not in cache:
        cache[keep_strings] = mask_non_code(source, keep_strings=keep_strings)
    return cache[keep_strings]
def resolve_solidify_mode(mode) -> SolidifyMode:
    if isinstance(mode, SolidifyMode):
        return mode
    candidate = mode.strip().lower() if isinstance(mode, str) else mode
    try:
        return SolidifyMode(candidate)
    except (TypeError, ValueError) as _mode_err:
        _log.warning("无效固化模式 %r，回退 %s (%s)", mode,
                     DEFAULT_SOLIDIFY_MODE.value, _mode_err)
        return DEFAULT_SOLIDIFY_MODE
class StaticSolidifier:
    def __init__(self) -> None:
        self.registry = SolidificationRegistry()
    def solidify_file(self, filepath,
                      mode: SolidifyMode = DEFAULT_SOLIDIFY_MODE) -> list:
        filepath_text = ""
        if isinstance(filepath, (str, bytes, os.PathLike)):
            filepath_text = os.fsdecode(os.fspath(filepath)).strip()
        if not filepath_text:
            _log.warning("solidify_file: 非法文件路径(%s)，跳过",
                         type(filepath).__name__)
            return []
        filepath = Path(filepath_text)
        mode = resolve_solidify_mode(mode)
        source, _fp = read_source_with_fingerprint(filepath_text)
        if source is None:
            _log.warning("跳过 %s: SSOT 通道读取失败", filepath)
            return []
        rule_types = _MODE_RULE_TYPES.get(mode)
        findings = []
        if rule_types is None or "ast" in rule_types:
            findings.extend(self._check_ast_rules(source, filepath))
        if rule_types is None or "regex" in rule_types:
            findings.extend(self._check_regex_rules(source, filepath))
        return findings
    def solidify_dir(self, root: str = ".",
                     mode: SolidifyMode = DEFAULT_SOLIDIFY_MODE) -> dict:
        active = collect_active_py_files(root)
        total = 0
        findings = []
        for py in active:
            points = self.solidify_file(py, mode=mode)
            findings.extend(points)
            total += len(points)
        return {"files": len(active), "solidification_points": total,
                "findings": findings}
    def _enabled_rules(self, pattern_type: str) -> list[SolidificationRule]:
        return [rule for rule in self.registry.list_rules(level=1)
                if rule.pattern_type == pattern_type and rule.enabled]
    def _check_ast_rules(self, source: str, filepath) -> list:
        findings = []
        try:
            tree = ast.parse(source)
        except PARSE_DEGRADE_EXC as _parse_exc:
            log_swallowed(
                __name__, _parse_exc,
                context=f'_check_ast_rules:{type(_parse_exc).__name__}')
            return findings
        cli_entry = is_cli_entry_module_source(source)
        for rule in self._enabled_rules("ast"):
            if rule.exempt_cli_entry and cli_entry:
                continue
            check_fn = AST_CHECKERS.get(rule.rule_id)
            if check_fn is None:
                if not pattern_matches_ast_heuristics(rule.pattern):
                    _log.debug("规则 %s 无可执行 AST 语义，跳过", rule.rule_id)
                    continue
                for node in iter_heuristic_matches(tree, rule.pattern):
                    findings.append(_rule_finding(
                        rule, filepath, getattr(node, "lineno", 0),
                        description=f"{rule.name}: {rule.pattern.lower()[:60]}"))
                continue
            check_fn(tree, rule, findings, filepath)
        return findings
    def _check_regex_rules(self, source: str, filepath) -> list:
        findings = []
        cli_entry = is_cli_entry_module_source(source)
        for rule in self._enabled_rules("regex"):
            if not rule.pattern:
                continue
            if rule.exempt_cli_entry and cli_entry:
                continue
            try:
                pattern = re.compile(rule.pattern)
            except (re.error, TypeError) as _re_err:
                _log.warning("规则 %s 的正则表达式无效: %s (%s)",
                             rule.rule_id, rule.pattern, _re_err)
                continue
            for line_no, _raw, match in iter_regex_matches(
                    source, pattern, code_only=rule.match_code_only):
                findings.append(_rule_finding(
                    rule, filepath, line_no, match=match.group()[:100]))
        return findings
_log.info("diag_solidify_rules 知识固化域已加载: %d 项导出", len(__all__))
_SOLIDIFY_FINGERPRINTS: dict[str, tuple[int, int] | None] = {}
def _solidify_loaded_key(skill_dir: str) -> str:
    text = ""
    if isinstance(skill_dir, (str, bytes, os.PathLike)):
        text = os.fsdecode(os.fspath(skill_dir)).strip()
    if not text:
        return ""
    return os.path.normcase(os.path.realpath(os.path.abspath(text)))
def _solidify_ssot_fingerprint(skill_dir: str) -> tuple[int, int] | None:
    if not _solidify_loaded_key(skill_dir):
        return None
    try:
        ssot_path = solidify_ssot_path(str(skill_dir))
        stat = os.stat(ssot_path)
    except FileNotFoundError:
        return None
    except (OSError, TypeError, ValueError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_solidify_ssot_fingerprint:{type(_swallowed_exc).__name__}')
        return None
    return (stat.st_mtime_ns, stat.st_size)
def invalidate_solidified_ssot(skill_dir: str) -> None:
    _key = _solidify_loaded_key(skill_dir)
    if not _key:
        return
    _SOLIDIFY_FINGERPRINTS.pop(_key, None)
_REGISTRY_SCOPE_RULES: dict[str, frozenset[str]] = {}
_REGISTRY_SCOPE_PENDING_RETIREMENTS: dict[str, frozenset[str]] = {}
_REGISTRY_SCOPE_LOCK = threading.RLock()
def _update_pending_scope_retirements(candidates: dict[str, set[str]],
                                      failed: set[str] | None) -> None:
    with _REGISTRY_SCOPE_LOCK:
        for scope_key, rule_ids in candidates.items():
            pending = rule_ids if failed is None else rule_ids & failed
            if pending:
                _REGISTRY_SCOPE_PENDING_RETIREMENTS[scope_key] = frozenset(pending)
            else:
                _REGISTRY_SCOPE_PENDING_RETIREMENTS.pop(scope_key, None)
def _bind_registry_scope(scope_key: str, registry) -> int:
    key = str(scope_key or "").strip()
    snapshot = getattr(registry, "scope_rule_ids", None)
    if not key or not callable(snapshot):
        return 0
    try:
        current = frozenset(snapshot())
    except Exception as _snapshot_exc:  # noqa: BLE001 — 快照不可用时不退休（保留原状）
        log_swallowed(
            __name__, _snapshot_exc,
            context=f'_bind_registry_scope:snapshot:{type(_snapshot_exc).__name__}')
        return 0
    candidates: dict[str, set[str]] = {}
    retired_keys: list[str] = []
    with _REGISTRY_SCOPE_LOCK:
        previous = _REGISTRY_SCOPE_RULES.get(key, frozenset())
        candidates.setdefault(key, set()).update(previous - current)
        for other_key in [k for k in _REGISTRY_SCOPE_RULES if k != key]:
            declared = _REGISTRY_SCOPE_RULES.pop(other_key)
            retired_keys.append(other_key)
            candidates.setdefault(other_key, set()).update(declared - current)
        for retired_key, declared in list(
                _REGISTRY_SCOPE_PENDING_RETIREMENTS.items()):
            candidates.setdefault(retired_key, set()).update(declared - current)
        _REGISTRY_SCOPE_RULES[key] = current
    for retired_key in retired_keys:
        invalidate_solidified_ssot(retired_key)
    foreign = {rule_id for rule_ids in candidates.values() for rule_id in rule_ids}
    if not foreign:
        _update_pending_scope_retirements(candidates, set())
        return 0
    try:
        det_registry = get_detector_registry()
    except Exception as _reg_exc:  # noqa: BLE001 — 注册表不可用时保留规则，不抛给调用方
        _update_pending_scope_retirements(candidates, None)
        log_swallowed(
            __name__, _reg_exc,
            context=f'_bind_registry_scope:get_registry:{type(_reg_exc).__name__}')
        return 0
    unregister = getattr(det_registry, "unregister", None)
    if not callable(unregister):
        _update_pending_scope_retirements(candidates, None)
        _log.warning("检测器注册表不支持退休接口，跨项目固化规则隔离跳过")
        return 0
    retired = 0
    failed: set[str] = set()
    for rule_id in sorted(foreign):
        try:
            if unregister(rule_id):
                retired += 1
        except Exception as _retire_exc:  # noqa: BLE001 — 单条退休失败不阻断其余规则
            failed.add(rule_id)
            log_swallowed(
                __name__, _retire_exc,
                context=f'_bind_registry_scope:unregister:{type(_retire_exc).__name__}')
    _update_pending_scope_retirements(candidates, failed)
    if retired:
        _log.info("[DiagRunner] 固化规则作用域切换: 退休失效项目私有规则%d条", retired)
    return retired
def load_solidified_ssot(skill_dir: str, force: bool = True) -> None:
    _key = _solidify_loaded_key(skill_dir)
    if not _key:
        _log.debug("[DiagRunner] SSOT加载: 空技能根，跳过")
        return
    _fingerprint: tuple[int, int] | None = None
    loaded = 0
    try:
        _fingerprint = _solidify_ssot_fingerprint(skill_dir)
        if (not force
                and _key in _SOLIDIFY_FINGERPRINTS
                and _SOLIDIFY_FINGERPRINTS[_key] == _fingerprint):
            with _REGISTRY_SCOPE_LOCK:
                scoped_rule_ids = _REGISTRY_SCOPE_RULES.get(_key)
                has_pending_scope = bool(
                    _REGISTRY_SCOPE_PENDING_RETIREMENTS
                    or any(scope_key != _key for scope_key in _REGISTRY_SCOPE_RULES))
            if scoped_rule_ids is not None and not has_pending_scope:
                det_registry = get_detector_registry()
                if all(det_registry.is_registered(rule_id)
                       for rule_id in scoped_rule_ids):
                    return
        reg = SolidificationRegistry()
        loaded = _load_ssot_into_registry(
            reg, solidify_ssot_path(str(skill_dir)))
        if loaded is None:
            _log.warning(
                "[DiagRunner] SSOT读取或结构校验失败：保留既有检测器作用域，"
                "不写入加载缓存")
            return
        synced = reg.sync_to_detector_registry()
        expected_synced = len(reg.scope_rule_ids())
        if synced != expected_synced:
            _SOLIDIFY_FINGERPRINTS.pop(_key, None)
            _log.warning(
                "[DiagRunner] 检测器同步不完整(%d/%d)：保留加载缓存失效状态，"
                "下次 force=False 将重试", synced, expected_synced)
            return
        if loaded > 0:
            _log.info("[DiagRunner] SSOT加载: %d条固化规则, %d条同步到检测器", loaded, synced)
        _bind_registry_scope(_key, reg)
    except Exception as e:  # noqa: BLE001 — SSOT 加载软失败不阻断诊断
        _SOLIDIFY_FINGERPRINTS.pop(_key, None)
        _log.warning("[DiagRunner] SSOT加载跳过（不阻断诊断）: %s", e)
    else:
        _SOLIDIFY_FINGERPRINTS[_key] = _fingerprint
def _load_solidify_registry(skill_dir: str) -> SolidificationRegistry | None:
    registry = SolidificationRegistry()
    if _solidify_loaded_key(skill_dir):
        loaded = _load_ssot_into_registry(
            registry, solidify_ssot_path(str(skill_dir)))
        if loaded is None:
            return None
    return registry
def _solidify_rules(skill_dir: str, result: dict,
                    findings: list) -> None:
    if not isinstance(result, dict):
        _log.warning("[Stage6d] 固化结果容器非 dict(%s)，跳过",
                     type(result).__name__)
        return
    if not _solidify_loaded_key(skill_dir):
        _log.warning("[Stage6d] 固化缺少可用技能根，跳过")
        return
    if not findings:
        return
    try:
        registry = _load_solidify_registry(skill_dir)
        if registry is None:
            _log.warning("[Stage6d] SSOT读取或结构校验失败，跳过固化并保留原文件")
            return
        se_result = SolidificationRuleGenerator().solidify_and_generate(
            findings, registry=registry, skill_dir=skill_dir)
        if (se_result.get("rules_created", 0) > 0
                or se_result.get("ssot_persisted")):
            _log.info("[Stage6d] 知识固化: %d规则, %d检测器, synced=%d",
                        se_result["rules_created"],
                        se_result.get("detectors_generated", 0),
                        se_result.get("detectors_synced", 0))
            result["_solidify_result"] = se_result
    except Exception as se_err:  # noqa: BLE001
        _log.warning("[Stage6d] 知识固化跳过: %s", se_err)
def _quality_disabled_rule_ids(quality: dict) -> list[str]:
    if not isinstance(quality, Mapping):
        return []
    disabled = quality.get("disabled_rules")
    if not isinstance(disabled, list):
        return []
    return [rule_id for rule_id in disabled
            if isinstance(rule_id, str) and rule_id]
def _commit_quality_adjustments(skill_dir: str, registry: Any,
                                quality: dict) -> None:
    disabled = _quality_disabled_rule_ids(quality)
    if not disabled:
        return
    try:
        persisted = bool(registry.persist_to_yaml(
            solidify_ssot_path(str(skill_dir))))
    except Exception as persist_err:  # noqa: BLE001 — 落盘异常回滚，不中断阶段6
        _log.warning("[Stage6d] 固化质量调整落盘异常: %s", persist_err)
        persisted = False
    quality["ssot_persisted"] = persisted
    if persisted:
        load_solidified_ssot(skill_dir, force=True)
        _log.info("[Stage6d] 固化质量调整落盘: %d个P3规则禁用", len(disabled))
        return
    for rule_id in disabled:
        rule = registry.find_by_rule_id(rule_id)
        if rule is not None:
            rule.enabled = True
    quality["disabled_rules"] = []
    quality["rules_adjusted"] = 0
    quality["persist_error"] = True
    _log.warning("[Stage6d] 固化质量调整落盘失败，已回滚%d个P3禁用",
                   len(disabled))
def _monitor_solidified_quality(skill_dir: str, result: dict,
                                findings: list) -> None:
    if not isinstance(result, dict):
        _log.warning("[Stage6d] 质量监控结果容器非 dict(%s)，跳过",
                     type(result).__name__)
        return
    if not _solidify_loaded_key(skill_dir):
        _log.warning("[Stage6d] 质量监控缺少可用技能根，跳过")
        return
    if not findings:
        return
    try:
        registry = _load_solidify_registry(skill_dir)
        if registry is None:
            _log.warning("[Stage6d] SSOT读取或结构校验失败，跳过质量调整")
            return
        quality = SolidificationReport.batch_quality_monitor(findings, registry)
        _commit_quality_adjustments(skill_dir, registry, quality)
        result["_solidify_quality_monitor"] = quality
        _log.info("[Stage6d] 固化质量: score=%.1f(%s), coverage=%.1f%%",
                    quality["quality_score"], quality["quality_grade"],
                    quality["coverage_rate"] * 100)
    except Exception as qm_err:  # noqa: BLE001
        _log.warning("[Stage6d] 固化质量监控跳过: %s", qm_err)
def run_stage6d_solidify(skill_dir: str, result: dict, findings: list) -> None:
    _solidify_rules(skill_dir, result, findings)
    _monitor_solidified_quality(skill_dir, result, findings)

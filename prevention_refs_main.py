from __future__ import annotations

import logging
import re
from dataclasses import dataclass, replace
from itertools import chain
from pathlib import Path

from jwsgj.diag_symbol_surface import (
    detect_hallucinated_api,
    detect_hallucinated_module,
    preflight_symbol_check,
)
from jwsgj.diag_types_defs import EntryResult, diag_issue_entry, diag_line
from jwsgj.diag_types_normalize import (
    as_sequence,
    coerce_line_number,
    severity_rank_of,
)
from jwsgj.fix_guide_rule_identity import get_fix_guidance
from jwsgj.hallucination_norms import verify_code_against_norms
from jwsgj.log_config import log_swallowed
from jwsgj.runtime_scope import PACKAGE_NAME
from jwsgj.skill_profile import detect_layout

__all__ = [
    'CHANNEL_SUFFIX',
    'CODE_REFS',
    'CODE_REFS_VERSION',
    'DETECTOR_ANCHOR_ALIAS',
    'DETECTOR_POOL_KEY_ALIAS',
    'DETECTOR_REF_ARTIFACT',
    'DETECTOR_REF_GATE3_ARCH',
    'DETECTOR_REF_QUALITY',
    'DETECTOR_REF_RECOVERED',
    'DETECTOR_REF_SECURITY',
    'DETECTOR_REF_STRING_JSON',
    'MAIN_CODE_REFS',
    'NET_ANCHOR_ALIAS',
    'CodeRef',
    'anchor_module',
    'attach_issue_examples',
    'build_keyed_registry',
    'enrich_diag_findings',
    'enrich_entry_result',
    'get_code_reference',
    'list_code_ref_rule_ids',
    'make_code_ref',
    'norm_rule_id',
    'preflight_api_check',
    'register_code_refs',
    'resolve_code_ref',
    'run_norms_gate',
    'run_write_preflight_gate',
    'series_counts',
    'series_names',
    'series_rule_ids',
]
_log = logging.getLogger(__name__)
_log.info("prevention_refs_main 主库七系列规则条目库已加载: %d 项导出", len(__all__))
def anchor_module(module: str) -> str:
    name = str(module or "").strip().strip(".")
    if not name:
        raise ValueError("anchor_module 需要非空模块名")
    return f"{PACKAGE_NAME}.{name}"
@dataclass(frozen=True)
class CodeRef:
    rule_id: str
    name: str
    bad_example: str
    good_example: str
    rationale: str
    detector_ref: str
    self_verifiable: bool = False
    severity: str = ""
    series: str = ""
    def __post_init__(self) -> None:
        for _field in (
            "rule_id", "name", "bad_example", "good_example",
            "rationale", "detector_ref",
        ):
            _value = getattr(self, _field)
            if not isinstance(_value, str):
                raise TypeError(
                    f"CodeRef 条目构造失败：rule_id={self.rule_id!r} 的 "
                    f"{_field} 类型为 {type(_value).__name__}；内容字段"
                    "声明为 str，非 str 值会在注册键、归一化回退匹配"
                    "（norm_rule_id）与系列标注（rid[:1]）处分别退化为"
                    "异形键/字符串化匹配/切片崩溃，必须在构造点拒绝。"
                )
            if not _value.strip():
                raise ValueError(
                    f"CodeRef 条目构造失败：rule_id={self.rule_id!r} 的 "
                    f"{_field} 为空；内容字段是示例注入与检测器溯源的"
                    "必需字段（空值会以空段流入注入渲染与 fix_example "
                    "输出，空 rule_id 是无法与 findings 对齐的死键），"
                    "请在构造点补齐。"
                )
        if not isinstance(self.self_verifiable, bool):
            raise TypeError(
                f"CodeRef 条目构造失败：rule_id={self.rule_id!r} 的 "
                f"self_verifiable 类型为 {type(self.self_verifiable).__name__}；"
                "该字段驱动自证分支，必须为 bool，字符串/整数真值会"
                "把声明与执行语义反转。"
            )
        for _field in ("series", "severity"):
            _value = getattr(self, _field)
            if not isinstance(_value, str):
                raise TypeError(
                    f"CodeRef 条目构造失败：rule_id={self.rule_id!r} 的 "
                    f"{_field} 类型为 {type(_value).__name__}；"
                    "series/severity 声明为 str 标签（允许空串表示未标注），"
                    "非 str 值会让 series_counts 以不可哈希值建键、"
                    "注入渲染输出非字符串标签，必须在构造点拒绝。"
                )
CODE_REFS: dict[str, CodeRef] = {}  # jwsgj:suppress E1-MUTABLE-GLOBAL TP-07 — 知识引用注册表，启动期一次性填充
CODE_REFS_VERSION = "1.3.6"
_DEFAULT_PROJECT_DIR = ""
_DEFAULT_SESSION_P0_COUNT = 0
def norm_rule_id(rid: str) -> str:
    return str(rid).strip().upper().replace("-", "").replace("_", "")
def _norm_label(value: str) -> str:
    return str(value or "").strip()
def _warn_unlabeled_refs(extra: dict[str, CodeRef], source: str) -> None:
    for _rid, _ref in extra.items():
        if (not _norm_label(_ref.series)
                or not _norm_label(_ref.severity)):
            _log.warning(
                "%s: 规则 %s 缺少 series/severity 标签，"
                "include_series 筛选与严重度排序将忽略该条目",
                source or "扩展模块", _rid,
            )
def _warn_norm_key_collisions(extra: dict[str, CodeRef], source: str) -> None:
    _norm_seen: dict[str, str] = {}
    for _rid in chain(CODE_REFS, extra):
        _nk = norm_rule_id(_rid)
        _owner = _norm_seen.setdefault(_nk, _rid)
        if _owner != _rid and _rid in extra:
            _log.warning(
                "%s: 规则号归一化碰撞: %s 与已注册 %s 同形（%s），"
                "归一化回退匹配仅能命中其一",
                source or "扩展模块", _rid, _owner, _nk,
            )
def _validate_key_types(extra: dict[str, CodeRef], source: str) -> None:
    _bad_type = sorted(
        repr(rid) for rid in extra if not isinstance(rid, str)
    )
    if _bad_type:
        raise TypeError(
            f"{source or '扩展模块'} 注册键类型错误（{_bad_type}）；"
            "register_code_refs 键须为规则号字符串（如 'B01'），"
            "请在构造点以 str rule_id 建键"
        )
def _validate_key_text(extra: dict[str, CodeRef], source: str) -> None:
    _blank = sorted(rid for rid in extra if not rid.strip())
    if _blank:
        raise ValueError(
            f"{source or '扩展模块'} 注册键为空/纯空白（{_blank}）；"
            "规则号是 findings 匹配与归一化回退的主键，"
            "请在构造点为条目补齐 rule_id"
        )
def _validate_ref_types(extra: dict[str, CodeRef], source: str) -> None:
    _invalid = {
        rid: v for rid, v in extra.items() if not isinstance(v, CodeRef)
    }
    if _invalid:
        _bad = ", ".join(
            f"{rid}={type(v).__name__}"
            for rid, v in sorted(_invalid.items())
        )
        raise TypeError(
            f"{source or '扩展模块'} 注册值类型错误（{_bad}）；"
            "register_code_refs 仅接受 CodeRef 条目，"
            "请在构造点用 CodeRef(...) 构造后再注册"
        )
def _validate_key_identity(extra: dict[str, CodeRef], source: str) -> None:
    _mismatch = sorted(
        (rid, ref.rule_id) for rid, ref in extra.items()
        if rid != ref.rule_id
    )
    if _mismatch:
        raise ValueError(
            f"{source or '扩展模块'} 注册键与条目 rule_id 不一致"
            f"（{_mismatch[:5]}）；CODE_REFS 以注册键为唯一索引，"
            "消费方按 findings 的 rule_id 回查，键值分裂会让条目永远查不到，"
            "请在构造点用 build_keyed_registry 以 ref.rule_id 建键"
        )
def _resolve_registration(extra: dict[str, CodeRef], source: str) -> dict[str, CodeRef]:
    _overlap = set(CODE_REFS) & set(extra)
    _true_conflict = {
        rid for rid in _overlap if CODE_REFS[rid] != extra[rid]
    }
    if _true_conflict:
        raise ValueError(
            f"{source or '扩展模块'} 与主库 CODE_REFS 规则号冲突"
            f"（内容不同）: {sorted(_true_conflict)}"
        )
    return {k: v for k, v in extra.items() if k not in _overlap}
def register_code_refs(extra: dict[str, CodeRef], source: str = "") -> None:
    if not isinstance(extra, dict):
        raise TypeError(
            f"{source or '扩展模块'} 注册容器类型错误"
            f"（{type(extra).__name__}）；register_code_refs 接受"
            " dict[str, CodeRef] 注册表（键=规则号），"
            "请在构造点以字典形式组织条目后注册"
        )
    if not extra:
        return
    _validate_key_types(extra, source)
    _validate_key_text(extra, source)
    _validate_ref_types(extra, source)
    _validate_key_identity(extra, source)
    _warn_unlabeled_refs(extra, source)
    _warn_norm_key_collisions(extra, source)
    _new = _resolve_registration(extra, source)
    if not _new:
        _log.debug(
            "%s: %d 条规则均已在主库 CODE_REFS（幂等跳过）",
            source or "扩展模块", len(extra),
        )
        return
    CODE_REFS.update(_new)
    _log.debug(
        "%s: 已合并 %d 条规则代码引用进主库 CODE_REFS",
        source or "扩展模块", len(_new),
    )
def get_code_reference(rule_id: str) -> CodeRef | None:
    if not isinstance(rule_id, str) or not rule_id:
        return None
    ref = CODE_REFS.get(rule_id)
    if ref is not None:
        return ref
    _want = norm_rule_id(rule_id)
    for _rid, _ref in CODE_REFS.items():
        if norm_rule_id(_rid) == _want:
            return _ref
    return None
_RULE_REF_ALIASES: dict[str, str] = {
    'O04': 'PF01',
    'BUG018': 'PL-01',
    'SEC008': 'PL-02',
    'REF012': 'PL-03',
    'PERF005': 'PL-04',
    'IMPLICITCONDITIONAL': 'IF-01',
    'IMPLICITLOOP': 'IF-01',
    'IMPLICITEXCEPTION': 'IF-01',
    'PYSYN': 'PY-10',
}
DETECTOR_ANCHOR_ALIAS: dict[str, str] = {
    'RD-05': 'TO-02', 'SC-01': 'TO-02',
    'RD-15': 'RF-01', 'D35-SILENT-FALLBACK': 'RF-01',
    'LG-01': 'D49', 'NC-01': 'NT-01', 'GL-01': 'TP-07',
    'MDA-01': 'RB-01', 'B101': 'AS-07', 'BANDIT-B101': 'AS-07',
    'SEC-02': 'RD-28', 'SEC-03': 'CF-02', 'hardcoded_credential': 'CF-02',
    'SEC-04': 'SE-10', 'SEC-05': 'SE-11', 'CM-01': 'RB-03', 'DB-01': 'DB-06',
    'RUFF-F811': 'DC-03', 'RUFF-B023': 'PL-01', 'RUFF-UP006': 'DP-04',
    'RUFF-UP045': 'DP-06', 'GF-09': 'IM-01', 'SEC-06': 'PT-01',
}
DETECTOR_POOL_KEY_ALIAS: dict[str, str] = {
    'RUFF-B023': 'PL-01',
}
NET_ANCHOR_ALIAS: dict[str, str] = {
    'NW-01': 'SE-23',
    'NW-02': 'SE-27',
    'B603': 'SE-38',
}
def resolve_code_ref(rule_id: str) -> CodeRef | None:
    ref = get_code_reference(rule_id)
    if ref is not None:
        return ref
    alias = _RULE_REF_ALIASES.get(norm_rule_id(rule_id))
    return get_code_reference(alias) if alias else None
def list_code_ref_rule_ids() -> list[str]:
    return list(CODE_REFS)
def build_keyed_registry(
    entries: list[CodeRef],
    registry_name: str,
) -> dict[str, CodeRef]:
    registry: dict[str, CodeRef] = {}
    for ref in entries:
        if not isinstance(ref, CodeRef):
            raise TypeError(
                f"{registry_name} 条目类型错误（{type(ref).__name__}）；"
                "build_keyed_registry 仅接受 CodeRef 条目，"
                "请在构造点用 CodeRef(...)/make_code_ref(...) 构造后再建键"
            )
        if ref.rule_id in registry:
            raise ValueError(f"{registry_name} 重复规则号: {ref.rule_id}")
        registry[ref.rule_id] = ref
    return registry
def _series_key(value: str) -> str:
    return _norm_label(value).casefold()
def series_counts(registry: dict[str, CodeRef]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for ref in registry.values():
        key = _series_key(ref.series)
        counts[key] = counts.get(key, 0) + 1
    return counts
def series_names(registry: dict[str, CodeRef]) -> list[str]:
    return list(dict.fromkeys(
        _series_key(ref.series) for ref in registry.values()))
def series_rule_ids(registry: dict[str, CodeRef], series: str) -> list[str]:
    want = _series_key(series)
    return sorted(
        rid for rid, ref in registry.items()
        if _series_key(ref.series) == want
    )
CHANNEL_SUFFIX = ' (Gate5 注册表 + preflight_diagnostic_check)'
DETECTOR_REF_SECURITY = (
    f"{anchor_module('diag_wiring_exc')} (SN01/SN02/SN04) + "
    f"{anchor_module('diag_rules_runtime')} (CV01) + "
    f"{anchor_module('diag_traps_coding')} (CC01/IA01/IA02/AW04/AW05) "
    "(DetectorRegistry: 编写时 preflight_diagnostic_check)"
)
DETECTOR_REF_STRING_JSON = (f"{anchor_module('diag_traps_payload')} "
                            "(DetectorRegistry: FM01-FM03 编写时 preflight_diagnostic_check)")
DETECTOR_REF_ARTIFACT = (
    f"{anchor_module('diag_traps_payload')} (DetectorRegistry: "
    "AT02/CF01/CF02/GF02 编写时 preflight_diagnostic_check；"
    "GF16/GF18 引擎委托留 diag_wiring_import_scan/"
    "diag_dependency_analyzer)"
)
DETECTOR_REF_QUALITY = (
    f"{anchor_module('diag_traps_coding')} (DetectorRegistry: CQ03/CQ06/CQ07) + "
    f"{anchor_module('diag_wiring_imports')} (UC01) + "
    f"{anchor_module('diag_gate_class_protocol')} (MM01) + "
    f"{anchor_module('diag_gate_io_control')} (DC01) "
    "(编写时 preflight_diagnostic_check)"
)
DETECTOR_REF_RECOVERED = (
    f"{anchor_module('diag_rules_runtime')} (FS02/LE03/LE04) + "
    f"{anchor_module('diag_runtime_objects')} (TH01/CL01) + "
    f"{anchor_module('diag_traps_async')} (X3) + "
    f"{anchor_module('diag_rules_expr_forms')} (NM02/NT01) "
    "(DetectorRegistry)")
DETECTOR_REF_GATE3_ARCH = (
    f"{anchor_module('diag_gate_arch')} (Gate3 DiagnoseGate 架构门禁规则域："
    "D 族单文件规则（导入与动态注册 D01/D02/D04/D06/D08/D13/D15/D27 + "
    "D_ARCH_CONSTRAINTS；语法卫生 D03/D07/D18/D23/D24/D25/D29 + 导出面 "
    "D48/D49）+ 规模规则 AS-09/SZ-02) + "
    f"{anchor_module('diag_structure_rules')} (切分与重复实现 "
    "D09/D12/D14/D21/D33 + D36) + "
    f"{anchor_module('diag_wiring_symbol_scan')} (跨技能目录依赖 D37)"
)
def make_code_ref(
    series: str,
    rule_id: str,
    name: str,
    severity: str,
    bad: str,
    good: str,
    rationale: str,
    detector_ref: str,
    self_verifiable: bool = True,
) -> CodeRef:
    ref = CodeRef(
        rule_id=rule_id,
        name=name,
        bad_example=bad,
        good_example=good,
        rationale=rationale,
        detector_ref=detector_ref,
        self_verifiable=self_verifiable,
        series=series,
        severity=severity,
    )
    for _field in ("series", "severity"):
        if not getattr(ref, _field).strip():
            raise ValueError(
                f"规则条目构造失败：rule_id={rule_id!r} 的 {_field} 为空；"
                "series/severity 为 include_series 筛选与严重度排序依赖"
                "的标签字段（条目构造点必填），请在构造点补齐。"
            )
    return ref
_GATE3_BUG = (
    f"{anchor_module('diag_gate_scope_bind')} (作用域/绑定 + 删除后引用域) + "
    f"{anchor_module('diag_gate_io_control')} (异常控制流 + 资源/编码生命周期 + IO 调用形态 + 死代码域) + "
    f"{anchor_module('diag_gate_class')} (B/O 类定义点契约 + 可变共享) + "
    f"{anchor_module('diag_gate_class_protocol')} (数据类成员 + 审计通道 + 异步/协议增补域) + "
    f"{anchor_module('diag_gate_loop')}（循环/终止性 B 族规则） + "
    f"{anchor_module('diag_gate_expr')}（表达式形态/字面量 B 族规则） + "
    f"{anchor_module('diag_gate_expr_flow')}（作用域/绑定状态 B 族规则）"
)
_GATE3_OVER = (f"{anchor_module('diag_gate_class')} "
               "(Gate3 DiagnoseGate O 族过度设计规则) + "
               f"{anchor_module('diag_gate_class_protocol')} (B/MM/D 规则)")
_GATE3_STUB = f"{anchor_module('cleanup_file_hygiene')} (Gate3 S系列规则、S系列扫描/盘点)"
_GATE4_NORM = f"{anchor_module('hallucination_norms')}.NormEngine (Gate4 幻觉规范)"
_FIX_POLICY_CHAIN = (
    f"{anchor_module('hallucination_prewrite')} (编写前 B35 约束注入)"
    f" + {anchor_module('diag_split_plan')} (编写时 Gate1 NO_PATCH_FIX 补丁形态"
    f"差集拦截) + {anchor_module('fix_safety_gate')}/treatment_experience (写前"
    f"补丁预检 L0 契约) + {anchor_module('ai_review_governance')} (AI 审核"
    "契约与校验 verdict 打回 fix_scope.no_patch_fix)"
)
def _b(
    rule_id: str, name: str, bad: str, good: str, rationale: str,
    severity: str = "",
) -> CodeRef:
    return CodeRef(
        rule_id=rule_id, name=name, bad_example=bad, good_example=good,
        rationale=rationale, detector_ref=_GATE3_BUG, self_verifiable=True,
        severity=severity,
    )
_BUG_REFS: list[CodeRef] = [
    _b('B01', '禁止可变默认参数',
       "def add_item(item, items=[]):\n"
       "    items.append(item)\n"
       "    return items",
       "def add_item(item, items=None):\n"
       "    if items is None:\n"
       "        items = []\n"
       "    items.append(item)\n"
       "    return items",
       '默认参数在函数定义时求值一次，跨调用共享同一可变对象，状态在调用间泄漏', severity='ERROR'),
    _b('B02', '禁止资源泄漏',
       "def read_config(path):\n"
       "    f = open(path, encoding='utf-8')\n"
       "    return f.read()",
       "def read_config(path):\n"
       "    with open(path, encoding='utf-8') as f:\n"
       "        return f.read()",
       '不使用 with 时关闭依赖引用计数/GC，异常或长生命周期引用会延迟释放文件句柄，长期运行可能耗尽资源', severity='ERROR'),
    _b('B03', '禁止裸 except',
       "def parse_int(text):\n"
       "    try:\n"
       "        return int(text)\n"
       "    except:\n"
       "        return 0",
       "def parse_int(text):\n"
       "    try:\n"
       "        return int(text)\n"
       "    except ValueError:\n"
       "        return 0",
       '裸 except 连 KeyboardInterrupt/SystemExit 一起吞掉，掩盖终止信号'),
    _b('B04', '禁止 finally 控制流',
       "def load(data):\n"
       "    try:\n"
       "        return int(data)\n"
       "    finally:\n"
       "        return -1",
       "def load(data):\n"
       "    try:\n"
       "        value = int(data)\n"
       "    except ValueError:\n"
       "        value = -1\n"
       "    return value",
       'finally 中的 return 会吞掉 try 块抛出的异常，静默改变控制流', severity='ERROR'),
    _b('B05', 'None 比较用 is',
       "def is_missing(value):\n"
       "    if value == None:\n"
       "        return True\n"
       "    return False",
       "def is_missing(value):\n"
       "    return value is None",
       '== 会调用 __eq__，对单例 None 应使用身份比较 is'),
    _b('B06', '禁止未使用变量',
       "def process(data):\n"
       "    total = sum(data)\n"
       "    count = len(data)\n"
       "    return total",
       "def process(data):\n"
       "    return sum(data)",
       '赋值后从未读取的变量是冗余代码或遗漏使用处的信号'),
    _b('B07', '禁止循环中修改迭代对象',
       "def drop_evens(items):\n"
       "    for item in items:\n"
       "        if item % 2 == 0:\n"
       "            items.remove(item)\n"
       "    return items",
       "def drop_evens(items):\n"
       "    return [item for item in items if item % 2 != 0]",
       '边遍历边 remove 会使迭代器跳过元素，结果不可预期', severity='ERROR'),
    _b('B08', '禁止 is 比较字面量',
       "def get_choice(code):\n"
       "    if code is 'A':\n"
       "        return 'Alpha'\n"
       "    return 'Unknown'",
       "def get_choice(code):\n"
       "    if code == 'A':\n"
       "        return 'Alpha'\n"
       "    return 'Unknown'",
       'is 是身份比较，字符串/数字字面量是否驻留属实现细节，跨解释器不可靠'),
    _b('B09', '禁止循环内字符串拼接',
       "def join_names(names):\n"
       "    result = ''\n"
       "    for name in names:\n"
       "        result += name + ','\n"
       "    return result",
       "def join_names(names):\n"
       "    return ''.join(name + ',' for name in names)",
       '字符串不可变，+= 每轮创建新对象，O(n^2)；join 一次构造 O(n)'),
    _b('B10', '禁止 __init__ 返回非 None',
       "class Box:\n"
       "    def __init__(self, value):\n"
       "        self.value = value\n"
       "        return value",
       "class Box:\n"
       "    def __init__(self, value):\n"
       "        self.value = value",
       '__init__ 返回非 None 触发 TypeError: __init__ should return None', severity='ERROR'),
    _b('B11', '禁止循环延迟绑定',
       "def build_handlers():\n"
       "    handlers = []\n"
       "    for i in range(3):\n"
       "        handlers.append(lambda: i * 2)\n"
       "    return handlers",
       "def build_handlers():\n"
       "    handlers = []\n"
       "    for i in range(3):\n"
       "        handlers.append(lambda i=i: i * 2)\n"
       "    return handlers",
       '闭包捕获变量名而非值，循环结束后所有闭包共享最后一次迭代的值', severity='ERROR'),
    _b('B12', '禁止可变类属性',
       "class Counter:\n"
       "    items = []\n"
       "\n"
       "    def add(self, item):\n"
       "        self.items.append(item)\n"
       "        return len(self.items)",
       "class Counter:\n"
       "    def __init__(self):\n"
       "        self.items = []\n"
       "\n"
       "    def add(self, item):\n"
       "        self.items.append(item)\n"
       "        return len(self.items)",
       '类体中的可变对象被所有实例共享，一个实例修改全部可见'),
    _b('B13', '禁止异常静默吞掉',
       "def load(path):\n"
       "    try:\n"
       "        return open(path, encoding='utf-8').read()\n"
       "    except OSError:\n"
       "        pass",
       "def load(path):\n"
       "    try:\n"
       "        with open(path, encoding='utf-8') as f:\n"
       "            return f.read()\n"
       "    except OSError as exc:\n"
       "        raise ValueError('无法读取: ' + path) from exc",
       'except 中 pass 掩盖真实错误，故障被推迟到难以定位的位置'),
    _b('B14', '禁止 type() 比较类型',
       "def describe(value):\n"
       "    if type(value) == str:\n"
       "        return 'text'\n"
       "    return 'other'",
       "def describe(value):\n"
       "    if isinstance(value, str):\n"
       "        return 'text'\n"
       "    return 'other'",
       'type()== 排除子类实例，破坏多态；isinstance 兼容继承链'),
    _b('B15', '禁止字面量除零',
       "def percent(value, total):\n"
       "    return value / 0",
       "def percent(value, total):\n"
       "    if total == 0:\n"
       "        return 0.0\n"
       "    return value / total",
       '除数为字面量 0 运行时必然抛 ZeroDivisionError，属确定性 BUG', severity='ERROR'),
    _b('B16', '禁止浮点等值比较',
       "def is_done(progress):\n"
       "    return progress == 1.0",
       "def is_done(progress):\n"
       "    return abs(progress - 1.0) < 1e-9",
       '二进制浮点有精度误差，== 比较在边界值上不可靠，应用误差范围'),
    _b('B17', '禁止迭代器复用',
       "def summarize(values):\n"
       "    it = iter(values)\n"
       "    first = list(it)\n"
       "    second = list(it)\n"
       "    return first, second",
       "def summarize(values):\n"
       "    items = list(values)\n"
       "    return items, list(items)",
       '迭代器一次性耗尽，第二次消费得到空结果；先物化为 list 再复用'),
    _b('B18', '禁止未绑定变量复合赋值',
       "def accumulate(values):\n"
       "    total += sum(values)\n"
       "    return total",
       "def accumulate(values):\n"
       "    total = 0\n"
       "    total += sum(values)\n"
       "    return total",
       '函数内 += 使变量成为局部名，未初始化即 UnboundLocalError', severity='ERROR'),
    _b('B19', '禁止命名遮蔽内置',
       "def first_item(items):\n"
       "    list = items\n"
       "    return list(items)[0]",
       "def first_item(items):\n"
       "    values = items\n"
       "    return list(values)[0]",
       '局部变量或参数遮蔽 list 等内置后，作用域内调用内置抛 TypeError；'
       '内部变量直接改名，公开参数改名须同步关键字调用方'),
    _b('B20', '禁止布尔冗余',
       "def is_valid(flag):\n"
       "    if flag:\n"
       "        return True\n"
       "    else:\n"
       "        return False",
       "def is_valid(flag):\n"
       "    return bool(flag)",
       'if/else 或 return True if c else False 仅构造布尔值时属冗余样板，直接 return bool(cond) 保持布尔返回类型'),
    _b('B21', '禁止原地方法返回值误用',
       "def sort_items(items):\n"
       "    return items.sort()",
       "def sort_items(items):\n"
       "    return sorted(items)",
       'sort/append 等原地方法返回 None，return 其结果得到 None', severity='ERROR'),
    _b('B22', '禁止忽略字符串方法返回值',
       "def clean(text):\n"
       "    text.strip()\n"
       "    return text",
       "def clean(text):\n"
       "    return text.strip()",
       '字符串不可变，strip 等返回新串，不赋值则修改无效'),
    _b('B23', '禁止 get 结果未判空解引用',
       "def get_city(user):\n"
       "    return user.get('address').city",
       "def get_city(user):\n"
       "    address = user.get('address')\n"
       "    if address is None:\n"
       "        return ''\n"
       "    return address.get('city', '')",
       'dict.get 缺键返回 None，链式解引用抛 AttributeError'),
    _b('B24', '禁止可变对象共享',
       "def make_grid(rows, cols):\n"
       "    return [[0] * cols] * rows",
       "def make_grid(rows, cols):\n"
       "    return [[0] * cols for _ in range(rows)]",
       '列表乘法是浅拷贝，外层所有元素指向同一个内层列表', severity='ERROR'),
    _b('B25', '异常转换须显式链接原因',
       "def load(path):\n"
       "    try:\n"
       "        return int(open(path, encoding='utf-8').read())\n"
       "    except OSError as exc:\n"
       "        raise RuntimeError('读取失败')",
       "def load(path):\n"
       "    try:\n"
       "        with open(path, encoding='utf-8') as f:\n"
       "            return int(f.read())\n"
       "    except OSError as exc:\n"
       "        raise RuntimeError('读取失败') from exc",
       '异常处理中直接 raise 会自动设置隐式 __context__ 并保留原堆栈；from exc 显式设置 __cause__，明确主动异常转换并避免与次生故障混淆'),
    _b('B26', '禁止未指定编码',
       "def read_text(path):\n"
       "    with open(path) as f:\n"
       "        return f.read()",
       "def read_text(path):\n"
       "    with open(path, encoding='utf-8') as f:\n"
       "        return f.read()",
       'open 缺 encoding 时 Windows 默认 GBK、Linux 默认 UTF-8，跨平台乱码'),
    _b('B27', '禁止循环变量遮蔽',
       "def print_grid(grid):\n"
       "    for row in grid:\n"
       "        for row in row:\n"
       "            print(row)",
       "def print_grid(grid):\n"
       "    for row in grid:\n"
       "        for cell in row:\n"
       "            print(cell)",
       '内外层循环变量同名，内层覆盖外层，语义混淆且易错'),
    _b('B28', '禁止返回内部可变状态',
       "class Bag:\n"
       "    def __init__(self):\n"
       "        self.items = []\n"
       "\n"
       "    def get_items(self):\n"
       "        return self.items",
       "class Bag:\n"
       "    def __init__(self):\n"
       "        self.items = []\n"
       "\n"
       "    def get_items(self):\n"
       "        return list(self.items)",
       '直接返回内部 list 引用，调用方可绕过封装修改内部状态'),
    _b('B29', '禁止 range(len()) 反模式',
       "def print_names(names):\n"
       "    for i in range(len(names)):\n"
       "        print(names[i])",
       "def print_names(names):\n"
       "    for name in names:\n"
       "        print(name)",
       '仅用索引读取元素时应直接迭代，需要索引时用 enumerate'),
    _b('B30', '禁止动态调用作默认参数',
       "from datetime import datetime\n"
       "\n"
       "\n"
       "def log_event(message, timestamp=datetime.now()):\n"
       "    print(timestamp, message)",
       "from datetime import datetime\n"
       "\n"
       "\n"
       "def log_event(message, timestamp=None):\n"
       "    if timestamp is None:\n"
       "        timestamp = datetime.now()\n"
       "    print(timestamp, message)",
       'datetime.now() 等在定义时求值一次，跨调用冻结同一时刻', severity='ERROR'),
    _b('B31', '禁止 assert 做参数校验',
       "def set_age(person, age):\n"
       "    assert age >= 0, 'age must be non-negative'\n"
       "    person['age'] = age\n"
       "    return person",
       "def set_age(person, age):\n"
       "    if age < 0:\n"
       "        raise ValueError('age must be non-negative')\n"
       "    person['age'] = age\n"
       "    return person",
       'python -O 优化模式下 assert 被剥离，校验静默失效'),
    _b('B32', '禁止遍历时删除/更新容器',
       "def drop_zeros(scores):\n"
       "    for name, score in scores.items():\n"
       "        if score == 0:\n"
       "            del scores[name]\n"
       "    return scores",
       "def drop_zeros(scores):\n"
       "    return {name: score for name, score in scores.items() if score != 0}",
       '遍历中改变容器大小触发 RuntimeError（dict）或跳元素（list）', severity='ERROR'),
    _b('B33', '禁止空容器判断用 len()',
       "def has_items(queue):\n"
       "    return len(queue) != 0",
       "def has_items(queue):\n"
       "    return bool(queue)",
       'len(x)==0 对内置容器冗余，truthiness（if not x）更简洁且兼容无 len 对象'),
    _b('B34', '禁止正则匹配结果未判空解引用',
       "import re\n"
       "\n"
       "\n"
       "def extract_year(text):\n"
       "    return re.search(r'\\d{4}', text).group(0)",
       "import re\n"
       "\n"
       "\n"
       "def extract_year(text):\n"
       "    match = re.search(r'\\d{4}', text)\n"
       "    return match.group(0) if match else ''",
       're.search 无匹配返回 None，直接 .group() 抛 AttributeError'),
    CodeRef(
        rule_id='B35', name='禁止补丁方式修复',
        bad_example=(
            "def sync_orders(api):\n"
            "    try:\n"
            "        return api.fetch_all()\n"
            "    except Exception:\n"
            "        return []  # 补丁式修复：吞掉超时/鉴权等一切错误伪装正常\n"
        ),
        good_example=(
            "import logging\n"
            "\n"
            "import requests\n"
            "\n"
            "log = logging.getLogger(__name__)\n"
            "\n"
            "\n"
            "def sync_orders(api):\n"
            "    try:\n"
            "        return api.fetch_all()\n"
            "    except requests.Timeout:\n"
            "        # 可降级错误：窄捕获 + 显式记录，返回标准失败信号 None\n"
            "        log.warning('fetch timeout, no snapshot this round')\n"
            "        return None\n"
            "    except requests.RequestException:\n"
            "        # 不可降级错误：上抛，根因不被遮蔽\n"
            "        raise\n"
        ),
        rationale=(
            '宽捕获静默吞以「看似正常」的返回值掩盖根因（超时/鉴权/配置），'
            '症状消失而根因仍在——补丁式修复；根因修复 = 可降级错误窄捕获+'
            '显式记录并返回标准失败信号，不可降级错误上抛，fixed_source 与'
            '根因分析可对应（四重强制链：编写前 B35 约束注入 → 编写时 '
            'diag_split_plan Gate1 补丁形态差集拦截 → apply_ai_fix 写前'
            '补丁预检 → AI 审核 verdict 打回）'
        ),
        detector_ref=_FIX_POLICY_CHAIN, self_verifiable=False,
        severity='ERROR',
    ),
]
_OVER_REFS: list[CodeRef] = [
    CodeRef(
        rule_id='O01', name='禁止单一实现抽象基类',
        bad_example=(
            "from abc import ABC, abstractmethod\n"
            "\n"
            "\n"
            "class Shape(ABC):\n"
            "    @abstractmethod\n"
            "    def area(self):\n"
            "        raise NotImplementedError\n"
            "\n"
            "\n"
            "class Circle(Shape):\n"
            "    def __init__(self, radius):\n"
            "        self.radius = radius\n"
            "\n"
            "    def area(self):\n"
            "        return 3.14159 * self.radius ** 2"
        ),
        good_example=(
            "def circle_area(radius):\n"
            "    # 只有一个实现时不需要抽象层，直接用函数\n"
            "    return 3.14159 * radius ** 2"
        ),
        rationale='抽象层缺少多态变化时是多余间接层，等第二个实现出现再抽象',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='O02', name='禁止无分支工厂',
        bad_example=(
            "def factory_parser(kind):\n"
            "    # 工厂只有一条分支，等价于直接构造\n"
            "    return JsonParser(kind)"
        ),
        good_example=(
            "class JsonParser:\n"
            "    def __init__(self, kind):\n"
            "        self.kind = kind\n"
            "\n"
            "\n"
            "class CsvParser:\n"
            "    def __init__(self, kind):\n"
            "        self.kind = kind\n"
            "\n"
            "\n"
            "def factory_parser(kind):\n"
            "    # 有真实分支选择时工厂才有价值\n"
            "    if kind == 'json':\n"
            "        return JsonParser(kind)\n"
            "    return CsvParser(kind)"
        ),
        rationale='无运行时分支的工厂是多余抽象，直接用构造函数',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='O03', name='禁止未使用参数',
        bad_example=(
            "def render(template, context, locale):\n"
            "    return template.format(**context)"
        ),
        good_example=(
            "def render(template, context, locale):\n"
            "    _ = locale  # 保留公开关键字契约，显式标记当前实现暂不使用\n"
            "    return template.format(**context)"
        ),
        rationale=('定义但未使用的参数属过度参数化（YAGNI），增加调用负担；'
                   '必须保留的参数应显式标记用途，不能为消除警告改名而破坏关键字调用契约'),
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='PF01', name='纯转发层（统一规则）',
        bad_example=(
            "def get_user(user_id):\n"
            "    # 函数体仅原样转发，无任何额外逻辑\n"
            "    return load_user(user_id)"
        ),
        good_example=(
            "def get_user(user_id):\n"
            "    # 包装层保留原签名，并叠加真实校验逻辑\n"
            "    user = load_user(user_id)\n"
            "    if user is None:\n"
            "        raise LookupError(user_id)\n"
            "    return user"
        ),
        rationale='仅原样转发的函数是多余间接层，直接调用底层函数',
        detector_ref=(f"{anchor_module('diag_pattern_rules')} "
                      '(DetectorRegistry: PF01 纯转发层统一规则)'),
        self_verifiable=False,
    ),
    CodeRef(
        rule_id='O05', name='禁止纯静态方法类',
        bad_example=(
            "class MathUtils:\n"
            "    @staticmethod\n"
            "    def add(a, b):\n"
            "        return a + b\n"
            "\n"
            "    @staticmethod\n"
            "    def mul(a, b):\n"
            "        return a * b"
        ),
        good_example=(
            "def add(a, b):\n"
            "    return a + b\n"
            "\n"
            "\n"
            "def mul(a, b):\n"
            "    return a * b"
        ),
        rationale='无实例状态的纯静态类应改为模块级函数，消除无意义的命名空间',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='O06', name='禁止单一方法类',
        bad_example=(
            "class Greeter:\n"
            "    def greet(self, name):\n"
            "        return 'hello ' + name"
        ),
        good_example=(
            "def greet(name):\n"
            "    return 'hello ' + name"
        ),
        rationale='仅一个无状态实例方法的类是多余抽象，改为函数',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='O07', name='禁止深层继承',
        bad_example=(
            "class A:\n"
            "    pass\n"
            "\n"
            "\n"
            "class B(A):\n"
            "    pass\n"
            "\n"
            "\n"
            "class C(B):\n"
            "    pass\n"
            "\n"
            "\n"
            "class D(C):\n"
            "    def value(self):\n"
            "        return 1\n"
            "\n"
            "\n"
            "class E(D):\n"
            "    pass"
        ),
        good_example=(
            "class Engine:\n"
            "    def start(self):\n"
            "        return True\n"
            "\n"
            "\n"
            "class Car:\n"
            "    # 组合替代超过 3 层的继承链\n"
            "    def __init__(self):\n"
            "        self.engine = Engine()"
        ),
        rationale='继承链超过 3 层产生脆弱基类问题，多数场景组合优于继承',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
    CodeRef(
        rule_id='O08', name='禁止冗余 getter/setter',
        bad_example=(
            "class User:\n"
            "    def __init__(self, name):\n"
            "        self.name = name\n"
            "\n"
            "    def get_name(self):\n"
            "        return self.name\n"
            "\n"
            "    def set_name(self, name):\n"
            "        self.name = name"
        ),
        good_example=(
            "class User:\n"
            "    def __init__(self, name):\n"
            "        self.name = name\n"
            "    # 无校验/无转换时直接访问属性；确需封装时用 @property"
        ),
        rationale='无逻辑的 getter/setter 是样板代码，Python 直接访问属性即可',
        detector_ref=_GATE3_OVER, self_verifiable=True,
    ),
]
_STUB_REFS: list[CodeRef] = [
    CodeRef(
        rule_id='S01', name='禁止自动添加兼容桩',
        bad_example=(
            "# old_loc.py：迁移后保留兼容桩\n"
            "from my_package.new_loc import Tool  # re-export 兼容旧导入路径\n"
            "__all__ = [\"Tool\"]"
        ),
        good_example=(
            "# 迁移后删除旧模块，消费者直接指向新位置\n"
            "from my_package.new_loc import Tool\n"
            "\n"
            "tool = Tool()"
        ),
        rationale='兼容桩掩盖真实依赖路径，累积成纯门户文件；默认应更新消费者 import',
        detector_ref=_GATE3_STUB, self_verifiable=False,
    ),
    CodeRef(
        rule_id='S02', name='禁止纯门户文件',
        bad_example=(
            "# 模块合并后原文件保留为纯 re-export 门户（禁止）\n"
            "from .impl import *"
        ),
        good_example=(
            "# 模块合并后删除原文件，消费者 import 直接指向 impl\n"
            "def real_logic(value):\n"
            "    return value * 2"
        ),
        rationale='纯 re-export 门户是死间接层，造成导入链膨胀与定位困难',
        detector_ref=_GATE3_STUB, self_verifiable=False,
    ),
    CodeRef(
        rule_id='S03', name='清理注释残留',
        bad_example=(
            "def compute(x):\n"
            "    # Re-export for backward compat\n"
            "    # === Auto-fix applied ===\n"
            "    return x + 1"
        ),
        good_example=(
            "def compute(x):\n"
            "    return x + 1"
        ),
        rationale='历史迁移注释残留误导后来者以为存在兼容负担，收尾时应清理',
        detector_ref=_GATE3_STUB, self_verifiable=False,
    ),
]
_NORM_REFS: list[CodeRef] = [
    CodeRef(
        rule_id='G2', name='禁止except:pass吞异常',
        bad_example=(
            "def run(cmd):\n"
            "    try:\n"
            "        print(cmd)\n"
            "    except Exception:\n"
            "        pass"
        ),
        good_example=(
            "def run(cmd):\n"
            "    try:\n"
            "        print(cmd)\n"
            "    except Exception as exc:\n"
            "        raise RuntimeError('执行失败') from exc"
        ),
        rationale='except:pass 吞掉一切异常，故障静默丢失；必须精确捕获并记录或向上传播',
        detector_ref=_GATE4_NORM, self_verifiable=True,
    ),
    CodeRef(
        rule_id='G3', name='禁止_前缀星号导入',
        bad_example=(
            "from os import *\n"
            "\n"
            "\n"
            "def crash():\n"
            "    # os._Environ 不在 os.__all__ 内，import * 不绑定它 → NameError\n"
            "    return _Environ"
        ),
        good_example=(
            "from os import _Environ\n"
            "\n"
            "\n"
            "def crash():\n"
            "    return _Environ"
        ),
        rationale='星号导入隐藏依赖来源，未声明 __all__ 的模块易引入命名冲突与幻觉引用',
        detector_ref=_GATE4_NORM, self_verifiable=True,
    ),
    CodeRef(
        rule_id='G1', name='禁止幻觉API',
        bad_example=(
            "def fetch_all(rows):\n"
            "    # fetch_all_rows 并不存在，AI 凭空脑补的 API\n"
            "    return fetch_all_rows(rows)"
        ),
        good_example=(
            "def fetch_all(rows):\n"
            "    # 只调用当前作用域或导入链中真实存在的函数\n"
            "    return [row for row in rows]"
        ),
        rationale='每个函数调用必须确认被调函数在作用域/导入链中存在，杜绝凭空脑补 API',
        detector_ref=_GATE4_NORM, self_verifiable=True,
    ),
    CodeRef(
        rule_id='G4', name='禁止不可执行代码',
        bad_example=(
            "# 反例：给出代码但不给验证方式，读者只能盲信\n"
            "print(\"已实现排序算法\")\n"
        ),
        good_example=(
            "# 正例：代码附验证方式，任何人可一键复核\n"
            "print(\"已实现排序算法\")  # 验证：python -c \"from x import sort; assert sort([3,1,2])==[1,2,3]\"\n"
        ),
        rationale='没有验证方式的代码片段等于不可执行的声明，错误会被静默复制扩散。每段代码附带可执行的验证命令（编译/导入/断言），让正确性可复核。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='G5', name='禁止未验证声称已实现',
        bad_example=(
            "# 反例：未运行就写「功能已完成，全部测试通过」\n"
        ),
        good_example=(
            "# 正例：先执行再声称——pytest -q tests/ 实际运行后引用真实输出\n"
            "# 「功能已完成：pytest 42 passed（2026-09-08 16:20 实测）」\n"
        ),
        rationale='未验证的完成声明是最危险的幻觉：它会终止所有后续核查。任何「已完成/PASS」声明必须附执行证据（命令+输出+时间），无证据不得声称。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='V1', name='compile 不用 ast.parse',
        bad_example=(
            "# 反例：用 ast.parse 验证语法（不编译，漏掉部分语法错误形态）\n"
            "ast.parse(src, name)\n"
        ),
        good_example=(
            "# 正例：compile 真正走编译器前端\n"
            "compile(src, name, \"exec\")\n"
        ),
        rationale='ast.parse 与 compile 的语法接受度不完全一致，ast.parse 通过不代表可编译执行。'
                  '语法验证统一用 compile(src, name, \'exec\')，与解释器真实口径对齐。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='V2', name='验证前清除 pyc 缓存',
        bad_example=(
            "# 反例：修改模块后直接 import 验证——旧 .pyc 缓存掩盖断裂\n"
            "import mymod  # 可能加载的是修改前的缓存字节码\n"
        ),
        good_example=(
            "# 正例：先清 __pycache__ 再验证\n"
            "import importlib\n"
            "import importlib.util\n"
            "import pathlib\n"
            "spec = importlib.util.find_spec(\"mymod\")\n"
            "if spec is None or spec.origin is None:\n"
            "    raise ImportError(\"mymod source not found\")\n"
            "for pyc in (pathlib.Path(spec.origin).parent / \"__pycache__\").glob(\"*.pyc\"):\n"
            "    pyc.unlink()  # 导入前逐文件清缓存，避免整目录级危险删除\n"
            "mod = importlib.import_module(\"mymod\")\n"
            "mod = importlib.reload(mod)\n"
        ),
        rationale='解释器可能加载修改前的缓存字节码，让断裂的导入链『通过』验证。任何导入链验证前先删 __pycache__，确保验证的是当前源码。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='V3', name='验证覆盖调用方',
        bad_example=(
            "# 反例：只验证定义存在，不验证调用方引用\n"
            "# def helper(): ... 定义检查通过即收工\n"
        ),
        good_example=(
            "# 正例：定义与调用双向验证\n"
            "# grep -rn \"from x import helper\" 每个消费文件逐个 import 成功\n"
        ),
        rationale='定义存在不代表调用链完好：改名/迁移后调用方的旧引用仍然断裂。符号变更时验证定义方与全部调用方，两侧都通过才算完成。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='V4', name='逐文件验证',
        bad_example=(
            "# 反例：10 个文件批量改完一起验证，一处 SyntaxError 淹没其余结论\n"
        ),
        good_example=(
            "# 正例：改一个→验证一个（compile+import）→再改下一个\n"
        ),
        rationale='批量修改后统一验证时，第一个错误会掩盖其余文件的真实状态，回滚定位成本剧增。逐文件修改、逐文件验证，每次只引入一个变量的不确定性。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='V5', name='修改前备份',
        bad_example=(
            "# 反例：直接改源文件，改坏了无回头路\n"
        ),
        good_example=(
            "# 正例：cp file.py file.py.bak 之后再编辑；或备份到独立目录\n"
        ),
        rationale='无备份的修改在出错时只能靠记忆恢复，双向编辑（AI 与人）场景下尤其危险。任何文件修改前先备份到工作区/临时目录，失败可整体回滚。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='V6', name='删除前验证功能迁移',
        bad_example=(
            "# 反例：判定死代码后直接删——消费者可能在字符串/反射里引用\n"
        ),
        good_example=(
            "# 正例：全仓 grep 符号名（含字符串与动态调用）确认零消费后再删\n"
            "# 删除后跑全量回归验证无断链\n"
        ),
        rationale='Python 的动态性（getattr/字符串导入/反射注册）使『看似零消费』的代码可能被隐性引用，删除即断链。删除前必须词级全仓扫描 + 删除后回归验证。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='M1', name='记录已实现前 AST 验证',
        bad_example=(
            "# 反例：凭印象写「已完成 add() 函数」\n"
        ),
        good_example=(
            "# 正例：先 ast.walk 确认函数真实存在\n"
            "import ast\n"
            "from pathlib import Path\n"
            "\n"
            "tree = ast.parse(Path(\"m.py\").read_text(encoding=\"utf-8\"))\n"
            "defined = {n.name for n in ast.walk(tree)\n"
            "           if isinstance(n, ast.FunctionDef)}\n"
            "if \"add\" not in defined:\n"
            "    raise RuntimeError(\"记忆失准：add() 未实现\")\n"
        ),
        rationale='记忆/报告中的『已实现』若未验证，就是幻觉的种子——它会误导后续所有决策。写入任何完成态记录前，用 AST/导入实际验证符号存在。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='M2', name='区分计划态与完成态',
        bad_example=(
            "# 反例：把 TODO 写得像完成了——「排序功能（待实现）支持百万级数据」\n"
        ),
        good_example=(
            "# 正例：状态显式分离——「[计划] 排序功能：目标支持百万级；[完成] 排序功能：实测 10 万级」\n"
        ),
        rationale='计划与完成混写会让读者把愿景当现状，后续基于错误前提推进。计划态带 TODO/目标标记，完成态带实测指标，永不混写。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='M3', name='summary 含校验锚点',
        bad_example=(
            "# 反例：「模块大幅重构，删除大量死代码」\n"
        ),
        good_example=(
            "# 正例：「模块从两千四百五十一行收敛到一千六百行，\n"
            "# 删除 FileCleaner 等六个零消费类，回归一千零四例全绿」\n"
        ),
        rationale='无量化锚点的摘要无法被快速复核，漂移无从发现。行数/函数数/PASS 数等指标写进摘要，任何人都可一条命令复核。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='M4', name='矛盾时必须更正',
        bad_example=(
            "# 反例：发现记忆说「函数已删除」但代码里还在——跳过不处理\n"
        ),
        good_example=(
            "# 正例：验证矛盾（grep+AST 确认现状）→ 更正记忆与代码状态对齐\n"
        ),
        rationale='被察觉却不更正的矛盾会持续放大：后续所有引用该记忆的决策都建立在错误地基上。发现记忆与实际状态不符时，先验证哪边为真，立即修正错误一侧。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='C1', name='人类必须审查 AI 代码',
        bad_example=(
            "# 反例：AI 生成代码直接合入主干\n"
        ),
        good_example=(
            "# 正例：AI 生成 → 门禁自动检查 → 人类 review 关键 diff → 合入\n"
        ),
        rationale='AI 代码的正确性是概率性的，无人审查的合入等于把未验证假设发布到生产。AI 生成代码必须经人类审查（至少关键路径 diff）后方可合入。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='C2', name='关键路径人工确认',
        bad_example=(
            "# 反例：自动执行 rm -rf / 移库 / 权限变更等不可逆操作\n"
        ),
        good_example=(
            "# 正例：高危操作清单 → 人工二次确认 → 留痕执行\n"
        ),
        rationale='安全相关/数据操作/不可逆操作一旦出错无法回滚，必须由人承担最终决策责任。高危操作（删除/覆盖/权限/外部副作用）执行前人工确认，AI 不得自主放行。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='C3', name='AI 声明不确定性',
        bad_example=(
            "# 反例：「这段代码肯定会正常工作」\n"
        ),
        good_example=(
            "# 正例：「置信度中：核心逻辑有测试覆盖，但并发场景未验证」\n"
        ),
        rationale='不声明置信度的输出会被人按确定性采信，风险被系统性低估。对生成的每段代码标注置信度（高/中/低）与未验证面。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='C4', name='负面约束优先',
        bad_example=(
            "# 反例：「写一个解析函数」（未说不能做什么，AI 可能引入 eval 等危险模式）\n"
        ),
        good_example=(
            "# 正例：「写一个解析函数；禁止 eval/exec，输入不可信，失败必须抛 ValueError」\n"
        ),
        rationale='先说要做什么而不说不要做什么，AI 会自行填补空白——经常填进危险默认值。先给负面清单（禁止项/边界），再给正面目标，约束住解空间。',
        detector_ref=_GATE4_NORM, self_verifiable=False, severity='P1',
    ),
    CodeRef(
        rule_id='R1', name='修改后对比基线',
        bad_example=(
            "# 反例：改完只看「没报错」就算完成\n"
        ),
        good_example=(
            "# 正例：修改后重跑诊断/测试，与修改前基线对比（findings 数/覆盖率/回归数）\n"
        ),
        rationale='『没报错』只说明没触发检查，不说明没引入退化——退化可能是静默的。修改前后各跑一次基线测量，对比差异确认无回退。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='R2', name='失败自动回滚',
        bad_example=(
            "# 反例：验证失败后留着半成品代码继续调试\n"
        ),
        good_example=(
            "# 正例：验证失败 → 从备份恢复原文件 → 分析原因 → 重新修改\n"
        ),
        rationale='半成品状态留在代码库里，下一个读者（人或 AI）会把它当稳定基线继续构建。验证失败立即回滚到备份，绝不带着失败状态前进。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
    CodeRef(
        rule_id='R3', name='3 次违规阻断会话',
        bad_example=(
            "# 反例：同一类错误反复出现 5 次，每次只道歉不改变流程\n"
        ),
        good_example=(
            "# 正例：累计 3 次同类违规 → 会话阻断，复盘根因后再继续\n"
        ),
        rationale='重复违规说明流程本身失效，继续执行只会放大损失。同类违规累计 3 次触发会话级阻断，强制先修流程再修代码。',
        detector_ref=_GATE4_NORM, self_verifiable=False,
    ),
]
_ARCH_REFS: list[CodeRef] = [
    CodeRef(
        rule_id='D01', name='函数内延迟导入',
        bad_example=(
            "def dump(data):\n"
            "    import json\n"
            "    return json.dumps(data)"
        ),
        good_example=(
            "import json\n"
            "\n"
            "\n"
            "def dump(data):\n"
            "    return json.dumps(data)"
        ),
        rationale='函数内 import 隐藏依赖，易致运行时 NameError 与性能抖动；循环依赖应重构模块边界而非下移 import',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
        severity='ERROR',
    ),
    CodeRef(
        rule_id='D03', name='兜底默认值返回',
        bad_example=(
            "def get_setting(key):\n"
            "    try:\n"
            "        return SETTINGS[key]\n"
            "    except Exception:\n"
            "        return 'default'"
        ),
        good_example=(
            "def get_setting(key):\n"
            "    return SETTINGS.get(key, 'default')"
        ),
        rationale='except 块返回硬编码默认值吞掉真实异常根因，故障不可见',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
    ),
    CodeRef(
        rule_id='D15', name='动态注册',
        bad_example=(
            "def register(name, obj):\n"
            "    globals()[name] = obj"
        ),
        good_example=(
            "_REGISTRY = {}\n"
            "\n"
            "\n"
            "def register(name, obj):\n"
            "    # 显式静态注册表替代 globals 注入\n"
            "    _REGISTRY[name] = obj"
        ),
        rationale='globals/sys.modules 动态注入绕过静态可分析性，诊断与补全失效',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
    ),
    CodeRef(
        rule_id='D23', name='自抛自接',
        bad_example=(
            "def parse(text):\n"
            "    try:\n"
            "        raise ValueError(text)\n"
            "    except ValueError:\n"
            "        return 0"
        ),
        good_example=(
            "def parse(text):\n"
            "    if not text.isdigit():\n"
            "        return 0\n"
            "    return int(text)"
        ),
        rationale='try 块 raise 又被同层 except 捕获是无效包装，徒增嵌套',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
    ),
    CodeRef(
        rule_id='D24', name='不可达 except',
        bad_example=(
            "def convert(value):\n"
            "    try:\n"
            "        return int(value)\n"
            "    except Exception:\n"
            "        return 0\n"
            "    except ValueError:\n"
            "        return -1"
        ),
        good_example=(
            "import logging\n"
            "\n"
            "_log = logging.getLogger(__name__)\n"
            "\n"
            "\n"
            "def convert(value):\n"
            "    try:\n"
            "        return int(value)\n"
            "    except ValueError:\n"
            "        # 可降级错误：窄捕获 + 显式告警 + 确定默认值\n"
            "        _log.warning('convert: 非法整数字面量 %r', value)\n"
            "        return -1\n"
            "    except Exception:\n"
            "        # 兜底分支同样留痕，不得静默吞错\n"
            "        _log.exception('convert: 未预期异常 %r', value)\n"
            "        return 0"
        ),
        rationale='宽泛 except Exception 在前会使后续具体 except 子句永不可达；具体异常分支前置，同时保留其他异常的后援处理',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
    ),
    CodeRef(
        rule_id='D27', name='死导入',
        bad_example=(
            "import os\n"
            "\n"
            "\n"
            "def add(a, b):\n"
            "    return a + b"
        ),
        good_example=(
            "def add(a, b):\n"
            "    return a + b"
        ),
        rationale='导入未使用的模块是死代码并掩盖真实依赖',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=True,
    ),
    CodeRef(
        rule_id='D02', name='静默降级导入无说明',
        bad_example=(
            "try:\n"
            "    from metrics_sdk import special_api\n"
            "except ImportError:\n"
            "    special_api = None  # 无注释：降级是刻意还是遗漏无从判断\n"
        ),
        good_example=(
            "try:\n"
            "    from metrics_sdk import special_api\n"
            "except ImportError:  # 刻意降级：可选依赖，缺省走本地实现\n"
            "    special_api = None\n"
        ),
        rationale='except ImportError 置 None 本身是合法容错，但无注释说明时，后续维护者无法区分刻意降级与意外断裂，'
                  '静默失效类缺陷（调用 None 属性崩溃）的排查成本成倍放大。降级必须留注释声明意图。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
        severity='INFO',
    ),
    CodeRef(
        rule_id='D04', name='疑似循环导入',
        bad_example=(
            "# a.py: from b import helper ; b.py: from a import config —— 鸡与蛋\n"
            "# 运行时 ImportError: cannot import name (partially initialized module)\n"
        ),
        good_example=(
            "# 依赖必须单向：把共享 config 下沉到 c.py，a/b 均从 c 导入\n"
            "# a.py: from c import config ; b.py: from c import config\n"
        ),
        rationale='环上模块互相导入时，先被加载的一方只能拿到部分初始化的命名空间，产生难以复现的 ImportError。设计时保证依赖图无环，共享依赖下沉到公共底层模块。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False, severity='ERROR',
    ),
    CodeRef(
        rule_id='D08', name='模块自引用导入',
        bad_example=(
            "# mymod.py\n"
            "import mymod  # 导入自身：初始化期间拿到部分初始化的模块对象\n"
        ),
        good_example=(
            "# mymod.py：自引用需求实为对自身常量/函数的引用，直接用本模块命名空间即可\n"
            "DEFAULT = 1\n"
            "def use():\n"
            "    return DEFAULT\n"
        ),
        rationale='模块导入自身会拿到部分初始化的模块对象（顶层语句尚未执行完），引用其属性时随机 NameError/AttributeError。'
                  '自身符号直接用，无需 import。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False, severity='ERROR',
    ),
    CodeRef(
        rule_id='D09', name='微型文件（不足二十行）',
        bad_example=(
            "# tiny_helper.py（全文仅三行）\n"
            "def clamp(v, lo, hi):\n"
            "    return max(lo, min(hi, v))\n"
        ),
        good_example=(
            "# 并入最近消费模块的既有文件（不新建 utils.py 等聚合文件）\n"
            "# 合并前补 pros/cons/net_benefit 论证（GOV-02）\n"
        ),
        rationale='行数不足二十的文件通常是拆分过度或残留碎片，每个文件都是一条导入链维护成本，微型文件聚集会显著抬高理解与导航成本。'
                  '按消费域并入既有模块；合并须经 GOV-02 论证，禁止新建聚合文件（GOV-01）。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
    ),
    CodeRef(
        rule_id='D12', name='碎片文件（比例失衡）',
        bad_example=(
            "# 一个两千行巨型主模块 + 十余个各一二十行的卫星碎片\n"
            "# 行数/函数/类比例失衡，职责边界模糊\n"
        ),
        good_example=(
            "# 卫星碎片并入其唯一消费域（既有模块）；主模块在既有边界内收敛职责：\n"
            "# 消除重复 / 收敛依赖 / 提取同模块私有实现，不按行数拆分\n"
        ),
        rationale='碎片文件与巨型主模块并存说明拆分粒度失控：碎片难以定位、巨型模块难以维护。'
                  '以消费关系为准绳重组——零消费碎片并入既有消费域，主模块通过消除重复与提取私有实现收敛职责，不新增文件/模块边界（GOV-01）。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
    ),
    CodeRef(
        rule_id='D13', name='导入结构违规（层级过深）',
        bad_example=(
            "from ..core.engines.registry.factory import make  # 四层上跳+深下钻\n"
        ),
        good_example=(
            "from my_package.registry import make  # 顶层包入口统一导出，依赖方向单一\n"
        ),
        rationale='深层相对导入把模块钉死在特定目录层级，任何移动/重命名都会撕裂导入链，且上跳式相对导入（..x）极易构成隐性环。统一走包顶层入口导出。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
    ),
    CodeRef(
        rule_id='D14', name='门面数量超标（导出>9）',
        bad_example=(
            "__all__ = [\"a\", \"b\", \"c\", \"d\", \"e\", \"f\", \"g\", \"h\", \"i\", \"j\", \"k\"]  # 11 项\n"
        ),
        good_example=(
            "__all__ = [\"core_api\", \"secondary_api\"]  # 按域聚合公开面 ≤ 9，内部符号私有化\n"
        ),
        rationale='单模块导出超过 9 项说明它聚合了过多职责，使用者需要在 11 个名字里猜正确入口，文档与测试面也随之膨胀。'
                  '收敛公共面：合并职责重复的导出、把仅内部使用的符号私有化，不新增子门面模块（GOV-01）。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
    ),
    CodeRef(
        rule_id='D29', name='语法错误',
        bad_example=(
            "# 反例：写盘前不做语法验证，src 若含语法错误（如 def broken(:）\n"
            "# 整模块不可导入，下游全部断链\n"
            "import pathlib\n"
            "\n"
            "def write_module(path, src):\n"
            "    pathlib.Path(path).write_text(src, encoding=\"utf-8\")\n"
        ),
        good_example=(
            "# 正例：写盘前 compile 验证，语法错误当场拒写\n"
            "import pathlib\n"
            "\n"
            "def write_module(path, src):\n"
            "    compile(src, path, \"exec\")  # SyntaxError 在写盘前抛出\n"
            "    pathlib.Path(path).write_text(src, encoding=\"utf-8\")\n"
        ),
        rationale='语法错误使整模块不可导入，所有依赖方级联断裂，属最高优先级阻断——任何写盘前必须 compile(src, name, \'exec\') 验证，失败即拒写。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False, severity='BLOCK',
    ),
    CodeRef(
        rule_id='D33', name='重复文件',
        bad_example=(
            "# v2/helper.py 与 helper.py 内容 90% 相同\n"
            "# 修 bug 只改了其中一份，另一份带着缺陷继续被消费\n"
        ),
        good_example=(
            "# 单一实现：helper.py 为 SSOT，v2 场景经参数/子类扩展，\n"
            "# 旧副本删除（S01：迁移后不留兼容桩）\n"
        ),
        rationale='双副本必然漂移：修复只落在一份，另一份成为带缺陷的活体。保持单一事实源（SSOT），扩展走参数化而非复制文件。',
        detector_ref=DETECTOR_REF_GATE3_ARCH, self_verifiable=False,
    ),
]
_SERIES_DBUG = "dbug"
_SERIES_DARCH = "darch"
_R_AUDIT_LOOP = (
    f"{anchor_module('diag_audit_container')} (D42 迭代就地突变审计检测器)"
)
_R_AUDIT = (
    f"{anchor_module('diag_audit_container')} (D44/D45/D46/D47 表达式结果与调用面误用) + "
    f"{anchor_module('diag_gate_class_protocol')} (D43 修复器终止性 + D54 类字段声明形态) + "
    f"{anchor_module('diag_wiring_imports')} (D53 模块级缺失导入) + "
    f"{anchor_module('diag_audit_none_guard')} (D52/D55) + "
    f"{anchor_module('diag_detector_assembly')} (DetectorRegistry 接线；"
    "审计编排通道 detect_all_audit_patterns 运行 D42-D47/D52-D55)"
)
_R_D43 = (
    f"{anchor_module('diag_gate_class_protocol')} (DetectorRegistry: D43 修复器终止性)"
)
_R_CORE = (f"{anchor_module('diag_detector_assembly')} "
           "(DetectorRegistry: D48/detect_all_overwrite、D49/detect_star_import)")
_R_CLASSES = (f"{anchor_module('diag_detector_assembly')} "
              "(DetectorRegistry: D36/D37/D40)")
_R_DELEG = (f"{anchor_module('diag_pattern_rules')} "
            "(DetectorRegistry: PF01 纯转发层统一规则；D50/D51 为细分来源)")
_R_ENGINE_F = (
    f"{anchor_module('engine_f_deadcode')} (F1 盲扫兜底占位项过滤) + "
    f"{anchor_module('build_refactor_plan')} "
    "(F5 重构候选：孤儿迁移测试消费/包门面证据与 M-06 吸收保护)；引擎内判定，无注册表规则号"
)
_R_ENGINE_F5 = (
    f"{anchor_module('build_refactor_plan')} (F5 重构候选：孤儿迁移测试消费/包门面证据"
    "与 M-06 吸收保护)；引擎内判定，无注册表规则号"
)
_R_FRAG = f"{anchor_module('diag_structure_rules')} (DetectorRegistry: AF01~AF04，目录级)"
_DBUG_REFS: list[CodeRef] = [
make_code_ref(
    _SERIES_DBUG, "D40", "空字典桩函数", "P2",
    'def load_config(path):\n'
    '    """加载配置。"""\n'
    '    if not path:\n'
    '        return {}\n'
    '    if path.endswith(".json"):\n'
    '        return {}\n'
    '    return {}\n',
    'import json\n'
    'import logging\n'
    'import pathlib\n'
    '\n'
    'def load_config(path):\n'
    '    """加载配置，空路径返回空 dict 并记日志。"""\n'
    '    if not path:\n'
    '        logging.getLogger(__name__).warning("load_config: empty path")\n'
    '        return {}\n'
    '    return json.loads(pathlib.Path(path).read_text(encoding="utf-8"))\n',
    "所有返回路径都返回空 dict 时函数是空壳桩，调用方拿到恒空数据被静默吞掉；"
    "至少一条路径返回真实数据或显式抛错/记日志。",
    _R_CLASSES,
),
make_code_ref(
    _SERIES_DBUG, "D42", "迭代中就地突变字典", "P1",
    'def prune_expired(cache):\n'
    '    """删除过期条目。"""\n'
    '    for key, val in cache.items():\n'
    '        if val["expired"]:\n'
    '            cache.pop(key)\n',
    'def prune_expired(cache):\n'
    '    """删除过期条目（先收集后删除，或迭代副本）。"""\n'
    '    for key in [k for k, v in cache.items() if v["expired"]]:\n'
    '        del cache[key]\n',
    "遍历 dict 时直接 pop/del 会触发 RuntimeError: dictionary changed size "
    "during iteration；应先收集待删键或迭代副本。",
    _R_AUDIT_LOOP,
),
make_code_ref(
    _SERIES_DBUG, "D43", "修复器 fix() 缺失 return", "P1",
    'class NameFixer:\n'
    '    """修复器。"""\n'
    '\n'
    '    def fix(self, lines):\n'
    '        """修复行内容。"""\n'
    '        if not lines:\n'
    '            return []\n'
    '        lines[0] = lines[0].replace("old", "new")\n',
    'class NameFixer:\n'
    '    """修复器。"""\n'
    '\n'
    '    def fix(self, lines):\n'
    '        """修复行内容。"""\n'
    '        if not lines:\n'
    '            return []\n'
    '        lines[0] = lines[0].replace("old", "new")\n'
    '        return lines\n',
    "fix/apply_fix 类修复方法某条分支执行了修改却不 return，调用方收不到"
    "结果（None），修复静默失效；所有代码路径必须显式返回。",
    _R_D43,
),
make_code_ref(
    _SERIES_DBUG, "D44", "容器元素改后未写回", "P2",
    'def fix_line(lines, idx):\n'
    '    """修复指定行。"""\n'
    '    new_line = lines[idx].replace("old", "new")\n'
    '    print(new_line)\n',
    'def fix_line(lines, idx):\n'
    '    """修复指定行并写回。"""\n'
    '    new_line = lines[idx].replace("old", "new")\n'
    '    lines[idx] = new_line\n'
    '    return lines\n',
    "str.replace/strip 等方法返回新字符串，从容器索引读出后修改却不写回"
    "容器（lines[idx] = new_line），修改结果被丢弃。",
    _R_AUDIT,
),
make_code_ref(
    _SERIES_DBUG, "D45", "无效表达式语句(no-op)", "P2",
    'def render(indent, text):\n'
    '    """拼接输出。"""\n'
    '    indent + text\n'
    '    return text\n',
    'def render(indent, text):\n'
    '    """拼接输出。"""\n'
    '    result = indent + text\n'
    '    return result\n',
    "表达式作为独立语句且无副作用（如 a + b、lines[0].replace(...)），"
    "实际什么都没做；多为漏写赋值目标，应赋值或写回。",
    _R_AUDIT,
),
make_code_ref(
    _SERIES_DBUG, "D46", "字符串 max/min 严重度语义错误", "P1",
    'def worst_level(levels):\n'
    '    """取最严重级别。"""\n'
    '    return max("INFO", "ERROR")\n',
    'def worst_level(levels):\n'
    '    """取最严重级别（按语义序而非字典序）。"""\n'
    '    order = {"INFO": 2, "WARN": 4, "ERROR": 5}\n'
    '    return max(levels, key=lambda s: order.get(s, 0))\n',
    'max("INFO", "ERROR") 按字典序返回 "INFO"（I>E），严重度语义恰好相反；'
    "严重度比较必须用显式语义序映射，禁止字符串字典序。",
    _R_AUDIT,
),
make_code_ref(
    _SERIES_DBUG, "D48", "__all__ 多次赋值覆盖", "P2",
    '__all__ = ["run_a", "run_b"]\n'
    '\n'
    'def run_a():\n'
    '    """A。"""\n'
    '    return "a"\n'
    '\n'
    'def run_b():\n'
    '    """B。"""\n'
    '    return "b"\n'
    '\n'
    '__all__ = ["run_a"]\n',
    '__all__ = ["run_a", "run_b"]\n'
    '\n'
    'def run_a():\n'
    '    """A。"""\n'
    '    return "a"\n'
    '\n'
    'def run_b():\n'
    '    """B。"""\n'
    '    return "b"\n',
    "__all__ 被第二次赋值后，第一次声明的条目被静默丢弃，导致导入丢失；"
    "公开符号清单只允许一处定义（可拼接扩展，不可整体覆盖）。",
    _R_CORE,
),
make_code_ref(
    _SERIES_DBUG, "D49", "星导入污染命名空间", "P2",
    'from os import *\n'
    'from os.path import *\n'
    '\n'
    'def join_dir(base, name):\n'
    '    """拼接路径。"""\n'
    '    return join(base, name)\n',
    'import os\n'
    '\n'
    'def join_dir(base, name):\n'
    '    """拼接路径。"""\n'
    '    return os.path.join(base, name)\n',
    "from X import * 污染命名空间、遮蔽内置名，且静态分析无法追踪符号来源"
    "（星导入不导入下划线前缀符号还会造成隐性丢失）；应显式导入。",
    _R_CORE,
),
make_code_ref(
    _SERIES_DBUG, "D50", "门面重导出/薄包装", "P3",
    'from my_package.core_impl import real_work as _impl_work\n'
    '\n'
    'work = _impl_work\n',
    'from my_package.core_impl import real_work\n'
    '\n'
    'result = real_work()  # 消费方直接调用真实实现，不再重导出\n',
    "重导出赋值（work = _impl_work）与薄包装器形成纯门面层，增加一层无"
    "意义的间接跳转；应让消费方直接导入真实符号。",
    _R_DELEG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DBUG, "D51", "可疑委托（无增值转发）", "P2",
    'scanner = build_scanner()\n'
    '\n'
    'def scan(code):\n'
    '    return scanner(code)\n',
    'scanner = build_scanner()\n'
    '\n'
    'def scan(code, extra_rules=None):\n'
    '    """扫描并附加增量规则聚合。"""\n'
    '    findings = scanner(code)\n'
    '    if extra_rules:\n'
    '        findings.extend(apply_extra(code, extra_rules))\n'
    '    return findings\n',
    "单行纯转发委托（return other(x)）无任何增值，徒增调用跳转与认知成本；"
    "委托必须叠加实质逻辑（参数加工/结果聚合/异常翻译）或直接删掉。",
    _R_DELEG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DBUG, "D52", "None-fallback 名直接调用", "P1",
    'fastjson = None\n'
    '\n'
    'def dumps(obj):\n'
    '    """序列化。"""\n'
    '    return fastjson.dumps(obj)\n',
    'import json\n'
    '\n'
    'try:\n'
    '    import fastjson\n'
    'except ImportError:  # 可选依赖缺失时降级为内置实现\n'
    '    fastjson = None\n'
    '\n'
    'def dumps(obj):\n'
    '    """序列化（带可用性守卫）。"""\n'
    '    if fastjson is None:\n'
    '        return json.dumps(obj)\n'
    '    return fastjson.dumps(obj)\n',
    "模块级 Name = None 作为可选依赖降级占位后，代码未经守卫直接调用会在依赖"
    "缺失时崩溃——Name(...) 名调用抛 TypeError、Name.ATTR(...) 属性链调用抛"
    "AttributeError；调用前必须 if Name is not None 守卫或提供降级实现。",
    _R_AUDIT,
),
make_code_ref(
    _SERIES_DBUG, "D53", "标准库模块未导入即使用", "P1",
    'def read_config(path):\n'
    '    """读配置。"""\n'
    '    return json.loads(read_text(path))\n'
    '\n'
    'def read_text(path):\n'
    '    """读文本。"""\n'
    '    return pathlib.Path(path).read_text(encoding="utf-8")\n',
    'import json\n'
    'import pathlib\n'
    '\n'
    'def read_config(path):\n'
    '    """读配置。"""\n'
    '    return json.loads(read_text(path))\n'
    '\n'
    'def read_text(path):\n'
    '    """读文本。"""\n'
    '    return pathlib.Path(path).read_text(encoding="utf-8")\n',
    "函数体内使用 module.attr 但模块未在文件级 import，导入时不报错、"
    "调用时 NameError（AI 生成代码的高频幻觉形态）；模块必须顶层导入。",
    _R_AUDIT,
),
make_code_ref(
    _SERIES_DBUG, "D55", "降级类方法返回 None", "P2",
    'class ParserFallback:\n'
    '    """解析降级实现。"""\n'
    '\n'
    '    def parse(self, text):\n'
    '        """解析。"""\n'
    '        return None\n',
    'from types import SimpleNamespace\n'
    '\n'
    'class ParserFallback:\n'
    '    """解析降级实现（保持主实现的属性返回契约）。"""\n'
    '\n'
    '    def parse(self, text):\n'
    '        """解析。"""\n'
    '        return SimpleNamespace(items=[], source=text)\n',
    "Fallback/Stub 类的方法直接 return None，调用方 .attr 访问触发 "
    "AttributeError；降级实现必须保持主实现的返回契约，按属性访问时返回具有同名字段的空结果对象，改返 dict 仍会造成契约断裂。",
    _R_AUDIT,
),
]
_DARCH_REFS: list[CodeRef] = [
make_code_ref(
    _SERIES_DARCH, "D36", "微型碎片文件(<20行)", "P2",
    '# helpers_io.py\n'
    'from my_package.core_io import read_text, write_text\n'
    '__all__ = ["read_text", "write_text"]\n',
    '# 直接在消费方模块 from my_package.core_io import read_text\n'
    '# 不再新建只做转发的 3 行碎片文件\n',
    "小于 20 行且只做转发的微型碎片文件徒增文件数与导入跳数；应并入消费方"
    "或主题主模块（目录级检测，仅注入引导）。",
    _R_CLASSES,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "D37", "跨技能目录依赖", "P2",
    'from other_skill_pkg.core import helper  # 依赖兄弟技能目录\n',
    '# 依赖本技能包内模块，公共能力下沉到共享库\n'
    'from my_package.shared import helper\n',
    "跨技能目录 import 会把两个技能的发布/演化耦合死，一端重构另一端断裂；"
    "公共能力应下沉共享库或复制内聚（文件级检测，仅注入引导）。",
    _R_CLASSES,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-01", "微型碎片文件/纯导入stub", "P2",
    '# constants_v2.py（全文仅 4 行常量转发）\n'
    'from constants import KEY_A, KEY_B\n'
    '__all__ = ["KEY_A", "KEY_B"]\n',
    '# 常量统一收口在 constants.py 单一 SSOT，不拆碎片转发文件\n',
    "碎片文件（<20 行）与纯导入 stub 是合并/删除候选；数量膨胀后同主题散落"
    "多文件、认知成本剧增（文件级检测，仅注入引导）。",
    _R_FRAG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-02", "同主题碎片聚集", "P2",
    '# 多个小文件消费同一主模块 helpers.py：\n'
    '# helpers_a.py / helpers_b.py / helpers_c.py 各 <20 行\n',
    '# 同主题小文件合并为单一 helpers.py，按节区分\n',
    "多个小文件消费同一主模块说明主题内聚未收口；应合并为单一主题模块"
    "（目录级检测，仅注入引导）。",
    _R_FRAG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-03", "目录碎片率超预警(>30%)", "P2",
    '# 目录内 >30% 文件为 <20 行碎片\n',
    '# 新建文件前先评估：能否并入既有主题模块？目录碎片率应 <30%\n',
    "目录碎片率超 30% 说明文件粒度失控；新建文件前评估并入既有模块"
    "（目录级检测，仅注入引导）。",
    _R_FRAG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-04", "目录碎片率超阻断(>50%)", "P0",
    '# 目录内 >50% 文件为 <20 行碎片\n',
    '# 强制收敛：碎片并入主题模块后再新增文件\n',
    "目录碎片率超 50% 属阻断级结构劣化；新建文件前必须先做碎片合并"
    "（目录级检测，仅注入引导）。",
    _R_FRAG,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-05", "发现通道占位项泛滥", "P1",
    '# 盲扫兜底把全量文件审查队列直接 append 进动作/发现汇总面\n'
    'for fp in all_files:\n'
    '    actions.append({"file": fp, "findings": []})  # 占位项\n',
    '# 占位审查队列留在子引擎 result 载荷供 AI 审查，不进汇总面\n'
    'if list_mode == "linked":\n'
    '    actions.extend(linked_items_with_findings)\n',
    "无明细占位项进入 findings 通道会把待审查文件数放大为等量伪发现，"
    "淹没真实问题并误导后续治疗优先级；"
    "动作/发现汇总面只收有可执行内容的条目，占位清单经 result 载荷透出"
    "（引擎内判定，仅注入引导）。",
    _R_ENGINE_F,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-06", "孤儿迁移判定无视测试消费与包门面", "P1",
    '# 唯一消费者只看生产 import 索引\n'
    'consumers = import_index.get(sym) - {src}\n'
    'if len(consumers) == 1:\n'
    '    migrate(sym, target=sole(consumers))  # tests/ 与 __init__ 门面未入判定\n',
    '# 迁移前并入测试消费证据并拒绝包入口目标\n'
    'for sym, target in candidates.items():\n'
    '    if sym in test_symbol_consumers.get(src, set()):\n'
    '        continue  # 迁移断裂模块↔测试同名套件\n'
    '    if Path(target).name == "__init__.py":\n'
    '        continue  # 包顶层是 lazy_imports 门面再导出层\n'
    '    migrate(sym, target)\n',
    "主扫描面排除 tests/ 时「唯一消费者」判定漏掉测试直接消费与包顶层"
    "再导出：迁移落地即断裂一对一测试或反转「实现居模块、顶层做门面」"
    "分层；迁移候选必须同时核验生产导入、测试消费与包入口角色。",
    _R_ENGINE_F5,
    self_verifiable=False,
),
make_code_ref(
    _SERIES_DARCH, "AF-07", "合并吸收有组外消费方的完整域", "P1",
    '# 仅凭同链高内聚就建议合并\n'
    'if cohesion >= 4.0 and same_chain:\n'
    '    suggest_merge(a, b)  # b 有组外消费方/数十KB完整域照并\n',
    '# 非组首成员零组外消费方且碎片尺寸才可吸收\n'
    'if (reverse_imports(m) - group) or size(m) >= 13 * 1024:\n'
    '    remove(m)  # 有组外消费方的吸收跨域改写导入链\n',
    "吸收有组外生产消费方的模块会跨域改写全部消费方导入链；吸收数十 KB"
    "完整域会抹平文档化分层；只有零组外消费方、保持公共契约且通过"
    "定向回归的碎片域，才可考虑吸收合并。",
    _R_ENGINE_F5,
    self_verifiable=False,
),
]
_MAIN_SERIES: dict[str, tuple[str, str]] = {
    "B": ("bug", "WARN"),
    "O": ("overdesign", "WARN"),
    "P": ("overdesign", "WARN"),
    "S": ("stub", "ERROR"),
    "G": ("norm", "P0"),
    "V": ("norm", "P0"),
    "M": ("norm", "P0"),
    "C": ("norm", "P0"),
    "R": ("norm", "P0"),
    "D": ("arch", "WARN"),
}
def _build_main_code_refs(entries: list[CodeRef] | None = None) -> dict[str, CodeRef]:
    if entries is None:
        entries = [
            *_BUG_REFS, *_OVER_REFS, *_STUB_REFS, *_NORM_REFS, *_ARCH_REFS,
            *_DBUG_REFS, *_DARCH_REFS,
        ]
    keyed = build_keyed_registry(entries, "MAIN_CODE_REFS")
    return {
        rid: _apply_main_series_tag(rid, ref)
        for rid, ref in keyed.items()
    }
def _apply_main_series_tag(rid: str, ref: CodeRef) -> CodeRef:
    series = _norm_label(ref.series)
    severity = _norm_label(ref.severity)
    default_series, default_severity = _MAIN_SERIES.get(rid[:1], ("", ""))
    series = series or default_series
    severity = severity or default_severity
    if not series or not severity:
        raise ValueError(
            f"MAIN_CODE_REFS 条目 {rid} 缺少 series/severity "
            f"标签（rule_id 首字母无 _MAIN_SERIES 映射，构造时须显式打标）"
        )
    return replace(ref, series=series, severity=severity)
MAIN_CODE_REFS: dict[str, CodeRef] = _build_main_code_refs()
register_code_refs(MAIN_CODE_REFS, "prevention_refs_main")
_FINDING_RULE_ID_KEYS = (
    "rule_id", "rule", "check_id", "ref_id", "check", "code",
    "type", "detector_id", "rule_ref", "id",
)
def _finding_rule_id(item: dict) -> str:
    for key in _FINDING_RULE_ID_KEYS:
        raw = item.get(key)
        if isinstance(raw, str) and raw.strip():
            return raw.strip()
    return ""
def _structured_finding_rule_id(item: dict) -> str:
    for key in ("check_id", "code"):
        raw = item.get(key)
        if isinstance(raw, str) and raw.strip():
            return raw.strip()
    return _finding_rule_id(item)
def _attach_fix_example(issue: dict) -> None:
    _rid = _structured_finding_rule_id(issue)
    if not _rid:
        return
    _ref = resolve_code_ref(_rid)
    if _ref is None:
        return
    _fill_ref_example_fields(issue, _ref)
def attach_issue_examples(issues) -> None:
    for issue in as_sequence(issues):
        if not isinstance(issue, dict):
            continue
        try:
            _attach_fix_example(issue)
        except Exception as e:
            _log.debug("[GenEntryGuard] 修复示例附加跳过: %s", e)
def _ref_example_fields(ref: CodeRef) -> dict[str, str]:
    return {
        "fix_example": ref.good_example,
        "bad_example": ref.bad_example,
        "rationale": ref.rationale,
        "detector_ref": ref.detector_ref,
    }
def _fill_ref_example_fields(item: dict, ref: CodeRef) -> None:
    for field, value in _ref_example_fields(ref).items():
        if not item.get(field):
            item[field] = value
def enrich_diag_findings(findings: list[dict] | None) -> list[dict]:
    return [_enrich_finding(item) for item in as_sequence(findings)
            if isinstance(item, dict)]
def _enrich_finding(item: dict) -> dict:
    new_item = dict(item)
    rule_id = _finding_rule_id(item)
    if not rule_id:
        return new_item
    ref = resolve_code_ref(rule_id)
    if ref is not None:
        _fill_ref_example_fields(new_item, ref)
    knowledge = _query_fix_knowledge(
        ref.rule_id if ref is not None else rule_id, item)
    if knowledge:
        new_item["knowledge"] = knowledge
    return new_item
def _query_fix_knowledge(rule_id: str, item: dict) -> str | None:
    try:
        return get_fix_guidance(rule_id, str(item.get("message") or ""))
    except Exception as e:
        _log.debug(
            "enrich_diag_findings: 规则 %s 知识查询降级: %s", rule_id, e)
        return None
_RULE_IN_RESULT_RE = re.compile(  # jwsgj:suppress SE-30 — 已压测最坏<0.2ms，无灾难性回溯
    r"^\[(?:反模式|规范|结构质量|诊断(?:预检)?)\]\s*"
    r"([^\s:]+)[^\n]*",
    re.MULTILINE,
)
_RESULT_LINE_RE = re.compile(r"\(行(\d+)\)\s*$")
def _result_text_line(text: str) -> int:
    matched = _RESULT_LINE_RE.search(text)
    return int(matched.group(1)) if matched else 0
def _append_rule_issue(issues: list[dict], seen: set[tuple[str, int]],
                       rule_id: str, message: str, severity: str,
                       line: int, suggestion: str = "") -> None:
    rule_id = str(rule_id or "").strip()
    if not rule_id:
        return
    ref = resolve_code_ref(rule_id)
    canonical_rule_id = ref.rule_id if ref is not None else rule_id
    key = (norm_rule_id(canonical_rule_id), line)
    if key in seen:
        return
    seen.add(key)
    _raw_severity = getattr(severity, "value", severity)
    _severity_text = str(_raw_severity).strip() if _raw_severity else ""
    _suggestion = str(suggestion or "")
    issues.append({
        "rule_id": canonical_rule_id,
        "message": str(message or ""),
        "severity": _severity_text or (ref.severity if ref is not None else ""),
        "line": line,
        "suggestion": (_suggestion or
                       (ref.good_example if ref is not None else "")),
    })
    if ref is not None:
        _fill_ref_example_fields(issues[-1], ref)
def _collect_structured_issues(result: EntryResult, issues: list[dict],
                               seen: set[tuple[str, int]]) -> None:
    for issue in chain(
        getattr(result, "gen_issues", None) or [],
        getattr(result, "diag_issues", None) or [],
    ):
        if not isinstance(issue, dict):
            continue
        _before_count = len(issues)
        _append_rule_issue(
            issues, seen, _structured_finding_rule_id(issue),
            issue.get("message", ""), issue.get("severity", ""),
            coerce_line_number(issue.get("line")),
            issue.get("suggestion", ""),
        )
        if len(issues) > _before_count:
            for _field, _value in issue.items():
                if _field in {"fix_example", "bad_example", "rationale",
                              "detector_ref"} and _value:
                    issues[-1][_field] = _value
def _collect_text_issues(result: EntryResult, issues: list[dict],
                         seen: set[tuple[str, int]]) -> None:
    text_pool = "\n".join(
        str(item)
        for item in (
            as_sequence(getattr(result, "errors", None))
            + as_sequence(getattr(result, "warnings", None))
        )
    )
    known_rule_ids = {norm_rule_id(issue["rule_id"]) for issue in issues}
    for match in _RULE_IN_RESULT_RE.finditer(text_pool):
        text = match.group(0)
        line = _result_text_line(text)
        matched_ref = resolve_code_ref(match.group(1))
        matched_rule_id = (
            matched_ref.rule_id if matched_ref is not None else match.group(1))
        if not line and norm_rule_id(matched_rule_id) in known_rule_ids:
            continue
        _append_rule_issue(
            issues, seen, match.group(1), text, "", line)
def enrich_entry_result(result: EntryResult) -> dict:
    issues: list[dict] = []
    seen: set[tuple[str, int]] = set()
    _collect_structured_issues(result, issues, seen)
    _collect_text_issues(result, issues, seen)
    decision = getattr(result, "decision", "")
    decision_value = getattr(decision, "value", decision)
    return {
        "ok": getattr(result, "ok", True),
        "decision": str(decision_value) if decision_value else "UNKNOWN",
        "filepath": getattr(result, "filepath", ""),
        "block_count": getattr(result, "block_count", 0),
        "issues": issues,
        "message": getattr(result, "message", ""),
    }
def _apply_norm_violation(violation: dict, result: EntryResult) -> int:
    raw_severity = violation.get("severity")
    is_blocking = severity_rank_of(raw_severity) == 0
    rule_id = violation.get("rule_id") or ""
    detail = violation.get("detail") or violation.get("name") or rule_id
    line_num = coerce_line_number(violation.get("line_num"))
    severity_text = str(
        getattr(raw_severity, "value", raw_severity) or ""
    ).strip()
    result.diag_issues.append(diag_issue_entry(
        rule_id, detail, severity_text, line_num,
        str(violation.get("suggestion") or ""),
    ))
    msg = diag_line("[规范]", rule_id, detail, line_num)
    if not is_blocking:
        result.warnings.append(msg)
        return 0
    result.record_blocked(msg)
    return 0 if norm_rule_id(rule_id) == "R3" else 1
def _degrade_preflight_blocked(result: EntryResult, label: str,
                               engine: str, exc: BaseException) -> None:
    result.degrade_gate("Gate4", label, engine, exc)
    result.record_blocked(
        f"[Gate4] {label}扫描未完成，覆盖不足，阻断写入: {exc}")

def run_norms_gate(code: str, filepath: str, result: EntryResult,
                   session_p0_count: int = _DEFAULT_SESSION_P0_COUNT) -> int:
    try:
        norm_result = verify_code_against_norms(
            code, filepath, session_p0_count=session_p0_count)
        return sum(
            _apply_norm_violation(v, result)
            for v in (norm_result.get("violations") or [])
            if isinstance(v, dict)
        )
    except Exception as e:
        log_swallowed(__name__, e, context='run_norms_gate:Exc')
        _degrade_preflight_blocked(result, "幻觉/规范", "", e)
        return 0
def _append_preflight_warnings(result: EntryResult, entries, *,
                              prefix: str, default_detail: str,
                              skip_kinds: frozenset | set = frozenset()) -> None:
    for _e in entries:
        if not isinstance(_e, dict):
            continue
        if _e.get("kind") in skip_kinds:
            continue
        _e_name = _e.get("name") or ""
        _e_line = _e.get("line")
        _e_loc = f" (行{_e_line})" if _e_line else ""
        _e_detail = _e.get("detail") or default_detail
        result.warnings.append(f"{prefix} {_e_name}{_e_loc}: {_e_detail}")
def run_write_preflight_gate(code: str, filepath: str, result: EntryResult, *,
                             project_dir: str = _DEFAULT_PROJECT_DIR,
                             session_p0_count: int = _DEFAULT_SESSION_P0_COUNT) -> int:
    p0_count = session_p0_count + run_norms_gate(
        code, filepath, result, session_p0_count)
    scan_errors: list[tuple[str, BaseException]] = []
    try:
        _suspicious, _symbol_findings = _scan_preflight_channels(
            code, project_dir or "", filepath, "", scan_errors=scan_errors)
        _append_preflight_warnings(
            result, _suspicious,
            prefix="[幻觉预检] 可疑API", default_detail="通用 API 清单未收录")
        _append_preflight_warnings(
            result, _symbol_findings,
            prefix="[符号预检] 项目符号幻觉", default_detail="",
            skip_kinds={"syntax_error"})
    except Exception as _pf_e:
        _degrade_preflight_blocked(result, "API/符号幻觉预检", "", _pf_e)
    for _channel, _exc in scan_errors:
        _degrade_preflight_blocked(result, "API/符号幻觉预检", _channel, _exc)
    return p0_count
def _as_preflight_item(finding) -> dict:
    line = getattr(finding, "line_num", None)
    if line is None:
        line = getattr(finding, "line", None)
    item = {
        "name": (getattr(finding, "name", "")
                 or getattr(finding, "title", "") or str(finding)),
        "line": line,
        "detail": (getattr(finding, "detail", "")
                   or getattr(finding, "description", "")),
    }
    kind = getattr(finding, "kind", None)
    if isinstance(kind, str) and kind:
        item["kind"] = kind
    module = getattr(finding, "module", None)
    if isinstance(module, str) and module:
        item["module"] = module
    return item
def _capture_scan_error(scan_errors: list[tuple[str, BaseException]] | None,
                        channel: str, exc: BaseException) -> None:
    if scan_errors is not None:
        scan_errors.append((channel, exc))

def _scan_suspicious_apis(
    code: str, filepath: str, *,
    scan_errors: list[tuple[str, BaseException]] | None = None,
) -> list[dict]:
    out: list[dict] = []
    try:
        for finding in detect_hallucinated_api(
                code, file_path=filepath or "<preflight>"):
            out.append(_as_preflight_item(finding))
    except Exception as e:
        _log.debug("preflight_api_check: API 存在性扫描降级跳过: %s", e)
        _capture_scan_error(scan_errors, "API 存在性", e)
    return out
def _scan_halluc_modules(
    code: str, project_dir: str, filepath: str, package: str, *,
    scan_errors: list[tuple[str, BaseException]] | None = None,
) -> list[dict]:
    out: list[dict] = []
    try:
        for finding in detect_hallucinated_module(
                code, filepath, project_dir=project_dir, package=package):
            out.append(_as_preflight_item(finding))
    except Exception as e:
        _log.debug("preflight_api_check: 幻觉模块扫描降级跳过: %s", e)
        _capture_scan_error(scan_errors, "幻觉模块", e)
    return out
def _scan_norm_violations(
    code: str, filepath: str, *,
    scan_errors: list[tuple[str, BaseException]] | None = None,
) -> list[dict]:
    try:
        norm_result = verify_code_against_norms(
            code, filepath or "<preflight>")
        return list(norm_result.get("violations", []))
    except Exception as e:
        _log.debug("preflight_api_check: 规范验证降级跳过: %s", e)
        _capture_scan_error(scan_errors, "规范验证", e)
        return []
def _top_level_package_dir(start: Path, root: Path) -> Path | None:
    current = start
    top: Path | None = None
    while current != root and current.is_relative_to(root):
        if not (current / "__init__.py").is_file():
            break
        top = current
        current = current.parent
    return top
def _package_import_context(
    package_root: Path, package_name: str,
) -> tuple[str, Path]:
    top = package_root
    while (top.parent != top
           and (top.parent / "__init__.py").is_file()):
        top = top.parent
    if top != package_root:
        package_name = ".".join(
            (top.name, *package_root.relative_to(top).parts))
    return package_name, top.parent
def _project_package_context(project_dir: str) -> tuple[str, str]:
    try:
        root = Path(project_dir).resolve()
        layout = detect_layout(str(root))
        if not layout.is_package or not layout.package_root:
            return "", project_dir
        package_root = Path(layout.package_root).resolve()
    except (OSError, RuntimeError, ValueError):
        return "", project_dir
    package_name, import_root = _package_import_context(
        package_root, layout.package_name)
    return package_name, str(import_root)
def _symbol_context_from_path(
    project_dir: str, filepath: str,
) -> tuple[str, str]:
    if not project_dir:
        return "", ""
    if not filepath or (filepath.startswith("<") and filepath.endswith(">")):
        return _project_package_context(project_dir)
    try:
        root = Path(project_dir).resolve()
        target = Path(filepath)
        if not target.is_absolute():
            target = root / target
        target = target.resolve()
        layout = detect_layout(str(root))
        package_root = (Path(layout.package_root).resolve()
                        if layout.is_package else None)
        package_name = layout.package_name if package_root else ""
        if package_root is not None and not target.parent.is_relative_to(
                package_root):
            package_root = None
            package_name = ""
        if package_root is None:
            package_root = _top_level_package_dir(target.parent, root)
            package_name = package_root.name if package_root else ""
        if package_root is not None and package_root.is_relative_to(root):
            package_name, import_root = _package_import_context(
                package_root, package_name)
            relative_parent = target.parent.relative_to(package_root)
            names = [package_name, *relative_parent.parts]
        else:
            import_root = root
            relative_parent = target.parent.relative_to(root)
            names = list(relative_parent.parts)
    except (OSError, RuntimeError, ValueError):
        return "", project_dir
    return ".".join(name for name in names if name), str(import_root)
def _scan_symbol_grounding(
    code: str, project_dir: str, package: str, filepath: str, *,
    import_root: str = "",
    scan_errors: list[tuple[str, BaseException]] | None = None,
) -> list[dict]:
    if not project_dir:
        return []
    if not import_root:
        derived_package, import_root = _symbol_context_from_path(
            project_dir, filepath)
        package = package or derived_package
    try:
        sym = preflight_symbol_check(
            code, import_root or project_dir, package=package)
        return list(sym.get("data", {}).get("findings", []))
    except Exception as e:
        _log.debug("preflight_api_check: 符号 grounding 降级跳过: %s", e)
        _capture_scan_error(scan_errors, "符号 grounding", e)
        return []
def _collect_norm_fix_hints(norm_violations: list[dict]) -> list[dict]:
    fix_hints: list[dict] = []
    seen_hint_ids: set[str] = set()
    for violation in norm_violations:
        if not isinstance(violation, dict):
            continue
        ref = resolve_code_ref(violation.get("rule_id", ""))
        if ref is not None and ref.rule_id not in seen_hint_ids:
            seen_hint_ids.add(ref.rule_id)
            fix_hints.append({
                "rule_id": ref.rule_id,
                "fix_example": ref.good_example,
                "rationale": ref.rationale,
            })
    return fix_hints
def _scan_preflight_channels(
    code: str, project_dir: str, filepath: str, package: str, *,
    scan_errors: list[tuple[str, BaseException]] | None = None,
) -> tuple[list[dict], list[dict]]:
    derived_package, import_root = (
        _symbol_context_from_path(project_dir, filepath)
        if project_dir else ("", ""))
    resolved_package = package or derived_package
    suspicious = (
        _scan_suspicious_apis(code, filepath, scan_errors=scan_errors)
        + _scan_halluc_modules(
            code, import_root or project_dir, filepath, resolved_package,
            scan_errors=scan_errors)
    )
    return suspicious, _scan_symbol_grounding(
        code, project_dir, resolved_package, filepath,
        import_root=import_root, scan_errors=scan_errors)
def preflight_api_check(code: str, project_dir: str = _DEFAULT_PROJECT_DIR,
                        *, package: str = "",
                        filepath: str = "") -> dict:
    scan_errors: list[tuple[str, BaseException]] = []
    suspicious, symbol_findings = _scan_preflight_channels(
        code, project_dir, filepath, package, scan_errors=scan_errors)
    norm_violations = _scan_norm_violations(
        code, filepath, scan_errors=scan_errors)
    fix_hints = _collect_norm_fix_hints(norm_violations)
    p0_violations = [
        v for v in norm_violations
        if isinstance(v, dict) and severity_rank_of(v.get("severity")) == 0
    ]
    return {
        "ok": (not scan_errors and not suspicious
               and not p0_violations and not symbol_findings),
        "scan_errors": [
            {"channel": channel, "error": f"{type(exc).__name__}: {exc}"}
            for channel, exc in scan_errors
        ],
        "suspicious_apis": suspicious,
        "norm_violations": norm_violations,
        "p0_violations": p0_violations,
        "fix_hints": fix_hints,
        "symbol_findings": symbol_findings,
    }

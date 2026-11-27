from __future__ import annotations

import ast
import copy
import glob
import hashlib
import json
import logging
import math
import os
import re
import threading
import time
from collections import OrderedDict
from collections.abc import Callable, Iterable
from dataclasses import dataclass
from typing import Any

from jwsgj.diag_shared_ast_nodes import (
    COMP_SCOPE_NODES,
    FUNC_NODE_TYPES,
    collect_param_names,
    comp_target_names,
    decision_points,
    decorator_name,
    expr_target_name,
    is_overload_stub,
    iter_scope_nodes,
)
from jwsgj.diag_shared_ast_views import register_cache_release
from jwsgj.diag_shared_source_core import (
    parse_cached,
    read_cached,
    read_source,
    source_digest,
)
from jwsgj.diag_types_normalize import (
    coerce_line,
    float_field,
    is_real_number,
    normalize_sources,
    parse_locator_file,
    parse_locator_line,
    plan_index,
    safe_float,
    str_or,
)
from jwsgj.diag_types_vocab import (
    FIELD_ADJUSTED_CONFIDENCE,
    PARSE_DEGRADE_EXC,
)
from jwsgj.fix_guide_rule_identity import (
    canonical_rule_id,
    get_fix_guidance,
)
from jwsgj.log_config import log_swallowed, write_module_run
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    get_temp_dir,
    is_path_within_skill,
    json_artifact_dir,
)
from jwsgj.runtime_scope import canonical_path
from jwsgj.xv_intermediate_store import (
    canonical_cv_path,
    load_cv_findings_index,
)

__all__ = [
    'FIXER_BLACKLIST',
    'FIXER_RISK_META',
    'FIXER_SIDE_EFFECTS',
    'CvContextIndex',
    'FunctionSummarizer',
    'SummaryCacheStats',
    'build_diagnosis_evidence',
    'build_dry_route_report',
    'check_fixer_blacklist',
    'clear_summary_cache',
    'default_regression_plan',
    'extract_code_context',
    'extract_code_context_in_project',
    'find_diag_snippet',
    'formalize_fix_precheck',
    'get_fixer_risk',
    'get_summary_cache_stats',
    'plan_fix_knowledge',
    'plan_single_fix',
    'revalidate_finding_line',
    'summarize_file',
    'summarize_function_at_line',
]
logger = logging.getLogger(__name__)
_MODULE_NAME = __name__.rsplit(".", 1)[-1]
_DEFAULT_SEVERITY = "P3"
_UNDECLARED = "未声明"
_DEFAULT_CODE_TO_WRITE = ""
def _path_arg(value: object) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, os.PathLike):
        try:
            raw = os.fspath(value)
        except TypeError as _e:
            log_swallowed(__name__, _e, context="_path_arg:TypeError")
            return ""
        return raw if isinstance(raw, str) else ""
    return ""
def _dict_items(value: object) -> list[dict]:
    if isinstance(value, (dict, str, bytes, bytearray)):
        return []
    if not isinstance(value, Iterable):
        return []
    try:
        return [item for item in value if isinstance(item, dict)]
    except (TypeError, ValueError, RuntimeError) as _e:
        log_swallowed(__name__, _e,
                      context=f"_dict_items:{type(_e).__name__}")
        return []
def _plan_id(finding: dict, rule_id: str, file_path: str,
             line_val: int) -> str:
    identity = {
        key: finding.get(key)
        for key in ("finding_id", "locator", "message", "code_snippet")
    }
    payload = json.dumps(
        [rule_id, file_path, line_val, identity],
        ensure_ascii=False, sort_keys=True, default=str,
        separators=(",", ":"),
    )
    id_suffix = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:6]
    return f"TREAT-PLAN-{int(time.time())}-{id_suffix}"
def plan_fix_knowledge(rule_id: str, message: str, code_snippet: str) -> dict:
    return {
        "fix_guidance": get_fix_guidance(rule_id, message),
        "fixer_risk": get_fixer_risk(rule_id),
        "fix_precheck": formalize_fix_precheck(rule_id, code_snippet),
        "rule_id_canonical": canonical_rule_id(rule_id),
    }
def default_regression_plan(
        file_path: str | None, configured: dict | None = None,
) -> dict[str, Any]:
    normalized = _path_arg(file_path)
    plan = {
        "full_regression": False,
        "targeted_tests": True,
        "verify_files": [normalized] if normalized else [],
    }
    if isinstance(configured, dict):
        plan.update(configured)
    plan["full_regression"] = False
    plan["targeted_tests"] = True
    return plan
def _finding_file_line(finding: dict, file_path, locator) -> tuple[str, int]:
    locator = str_or(finding.get("locator"), "") or str_or(locator, "")
    resolved_file = (
        _path_arg(file_path)
        or _path_arg(finding.get("file"))
        or _path_arg(finding.get("file_path"))
        or _path_arg(parse_locator_file(locator))
    )
    line_val = coerce_line(finding.get("line", 0))
    if line_val <= 0:
        line_val = parse_locator_line(locator)
    return resolved_file, line_val
def plan_single_fix(finding: dict | None = None, file_path: str | None = None) -> dict:
    finding = finding if isinstance(finding, dict) else {}
    locator = str_or(finding.get("locator"), "")
    file_path, line_val = _finding_file_line(finding, file_path, locator)
    rule_id = str_or(finding.get("rule_id"), "")
    message = str_or(finding.get("message"), "")
    code_snippet = str_or(finding.get("code_snippet"), "")
    raw_finding = finding.get("raw_finding")
    return {
        "plan_id": _plan_id(finding, rule_id, file_path, line_val),
        "rule_id": rule_id,
        "file": file_path,
        "line": line_val,
        "severity": str_or(finding.get("severity"), "") or _DEFAULT_SEVERITY,
        "message": message,
        "code_snippet": code_snippet,
        "locator": locator,
        "raw_finding": raw_finding if isinstance(raw_finding, dict) else {},
        "has_fixer": False,
        "fixer_name": "",
        "fixer_tier": "",
        "auto_safe": False,
        "fixer_type": "no_fixer",
        "strategy": "manual_ai",
        "dev_fixer_assessment": None,
        "regression_plan": default_regression_plan(file_path),
        "status": "pending_ai_review",
        "ai_action": "AI 审核本方案并手动执行修复，再验证",
        **plan_fix_knowledge(rule_id, message, code_snippet),
    }
FIXER_RISK_META: dict[str, dict] = {
    "DP-05": {"reliability": "high", "auto_safe": True},
    "DP-07": {"reliability": "high", "auto_safe": True},
    "DP-10": {"reliability": "high", "auto_safe": True},
    "DP-13": {"reliability": "medium", "auto_safe": True},
    "DP-32": {"reliability": "high", "auto_safe": True},
    "DP-39": {"reliability": "high", "auto_safe": True},
    "DP-41": {"reliability": "high", "auto_safe": True},
    "DP-42": {"reliability": "high", "auto_safe": True},
    "DP-45": {"reliability": "high", "auto_safe": True},
    "DP-48": {"reliability": "high", "auto_safe": True},
    "DP-49": {"reliability": "high", "auto_safe": True},
    "DP-50": {"reliability": "high", "auto_safe": True},
    "DP-51": {"reliability": "medium", "auto_safe": True},
    "DP-52": {"reliability": "high", "auto_safe": True},
    "DP-53": {"reliability": "high", "auto_safe": True},
    "DP-01": {"reliability": "medium", "auto_safe": False},
    "DP-02": {"reliability": "medium", "auto_safe": False},
    "DP-03": {"reliability": "medium", "auto_safe": False},
    "DP-08": {"reliability": "medium", "auto_safe": False},
    "DP-09": {"reliability": "medium", "auto_safe": False},
    "DP-11": {"reliability": "low", "auto_safe": False},
    "DP-12": {"reliability": "medium", "auto_safe": False},
    "DP-22": {"reliability": "medium", "auto_safe": False},
    "DP-23": {"reliability": "medium", "auto_safe": False},
    "DP-24": {"reliability": "medium", "auto_safe": False},
    "DP-33": {"reliability": "low", "auto_safe": False},
    "DP-35": {"reliability": "medium", "auto_safe": False},
    "DP-36": {"reliability": "medium", "auto_safe": False},
    "DP-37": {"reliability": "medium", "auto_safe": False},
    "DP-38": {"reliability": "medium", "auto_safe": False},
    "DP-40": {"reliability": "medium", "auto_safe": False},
    "DP-43": {"reliability": "medium", "auto_safe": False},
    "DP-44": {"reliability": "medium", "auto_safe": False},
    "DP-46": {"reliability": "medium", "auto_safe": False},
    "DP-47": {"reliability": "medium", "auto_safe": False},
    "DP-54": {"reliability": "medium", "auto_safe": False},
    "DP-55": {"reliability": "medium", "auto_safe": False},
    "RB-01": {"reliability": "high", "auto_safe": True},
    "RB-03": {"reliability": "medium", "auto_safe": True},
    "RB-11": {"reliability": "medium", "auto_safe": True},
    "RB-04": {"reliability": "medium", "auto_safe": False},
    "RB-14": {"reliability": "medium", "auto_safe": False},
    "RD-01": {"reliability": "medium", "auto_safe": True},
    "RD-03": {"reliability": "high", "auto_safe": True},
    "RD-05": {"reliability": "medium", "auto_safe": True},
    "RD-06": {"reliability": "medium", "auto_safe": False},
    "RD-08": {"reliability": "medium", "auto_safe": False},
    "RD-12": {"reliability": "medium", "auto_safe": False},
    "RD-15": {"reliability": "medium", "auto_safe": False},
    "RD-17": {"reliability": "medium", "auto_safe": False},
    "RD-19": {"reliability": "low", "auto_safe": False},
    "RD-23": {"reliability": "low", "auto_safe": False},
    "NT-01": {"reliability": "high", "auto_safe": True},
    "BZ-01": {"reliability": "high", "auto_safe": True},
    "DG-01": {"reliability": "high", "auto_safe": True},
    "IC-01": {"reliability": "high", "auto_safe": True},
    "DG-02": {"reliability": "medium", "auto_safe": False},
    "EX-08": {"reliability": "high", "auto_safe": True},
    "NS-01": {"reliability": "high", "auto_safe": False},
    "X3": {"reliability": "high", "auto_safe": True},
    "FS-02": {"reliability": "high", "auto_safe": True},
    "EP-02": {"reliability": "medium", "auto_safe": False},
    "TY-02": {"reliability": "high", "auto_safe": True},
    "DF-03": {"reliability": "high", "auto_safe": True},
    "SC-01": {"reliability": "medium", "auto_safe": True},
    "LK-02": {"reliability": "medium", "auto_safe": False},
    "LK-03": {"reliability": "medium", "auto_safe": False},
    "FL-01": {"reliability": "high", "auto_safe": True},
    "TY-03": {"reliability": "high", "auto_safe": True},
    "TP-26": {"reliability": "medium", "auto_safe": True},
    "SP-01": {"reliability": "high", "auto_safe": True},
    "TP-07": {"reliability": "medium", "auto_safe": False},
    "TP-05": {"reliability": "medium", "auto_safe": True},
    "FS-01": {"reliability": "medium", "auto_safe": False},
    "LG-01": {"reliability": "low", "auto_safe": True},
    "WC-01": {"reliability": "medium", "auto_safe": True},
    "EN-01": {"reliability": "medium", "auto_safe": True},
    "B09": {"reliability": "medium", "auto_safe": True},
    "CM-01": {"reliability": "medium", "auto_safe": False},
    "DB-01": {"reliability": "medium", "auto_safe": False},
    "FN-01": {"reliability": "medium", "auto_safe": False},
    "GL-01": {"reliability": "medium", "auto_safe": False},
    "MC-01": {"reliability": "low", "auto_safe": False},
    "RC-01": {"reliability": "low", "auto_safe": False},
    "RL-01": {"reliability": "medium", "auto_safe": False},
    "TX-01": {"reliability": "medium", "auto_safe": False},
    "TY-01": {"reliability": "medium", "auto_safe": True},
    "GF-07": {"reliability": "high", "auto_safe": True},
    "GF-02": {"reliability": "high", "auto_safe": True},
    "SL-06": {"reliability": "medium", "auto_safe": False},
    "unbounded_recursion": {"reliability": "medium", "auto_safe": False},
    "missing_docstring": {"reliability": "medium", "auto_safe": True},
    "deep_nesting": {"reliability": "high", "auto_safe": True},
    "module_level_call": {"reliability": "high", "auto_safe": True},
    "todo_marker": {"reliability": "high", "auto_safe": True},
    "SE-20": {"reliability": "medium", "auto_safe": False},
    "conditional_import": {"reliability": "high", "auto_safe": True},
    "danger_pattern": {"reliability": "medium", "auto_safe": True},
    "priority_recommendation": {"reliability": "high", "auto_safe": True},
    "SB-01": {"reliability": "high", "auto_safe": True},
    "BC-01": {"reliability": "low", "auto_safe": False},
    "SEC-01": {"reliability": "low", "auto_safe": False},
    "SEC-02": {"reliability": "low", "auto_safe": False},
    "SEC-03": {"reliability": "medium", "auto_safe": False},
    "SEC-04": {"reliability": "low", "auto_safe": False},
    "SEC-05": {"reliability": "low", "auto_safe": False},
    "SEC-06": {"reliability": "low", "auto_safe": False},
    "SEC-GEN": {"reliability": "low", "auto_safe": False},
    "B101": {"reliability": "low", "auto_safe": False},
    "NC-01": {"reliability": "high", "auto_safe": True},
    "MDA-01": {"reliability": "high", "auto_safe": True},
    "GF-01": {"reliability": "high", "auto_safe": True},
    "GF-03": {"reliability": "high", "auto_safe": True},
    "GF-04": {"reliability": "medium", "auto_safe": False},
    "GF-06": {"reliability": "medium", "auto_safe": False},
    "GF-08": {"reliability": "medium", "auto_safe": False},
    "GF-09": {"reliability": "high", "auto_safe": True},
    "GF-10": {"reliability": "medium", "auto_safe": False},
    "GF-12": {"reliability": "low", "auto_safe": False},
    "GF-14": {"reliability": "low", "auto_safe": False},
    "GF-15": {"reliability": "low", "auto_safe": False},
    "GF-16": {"reliability": "medium", "auto_safe": False},
    "GF-17": {"reliability": "medium", "auto_safe": False},
    "GF-18": {"reliability": "medium", "auto_safe": True},
    "GF-19": {"reliability": "medium", "auto_safe": True},
    "SZ-02": {"reliability": "high", "auto_safe": False},
    "CQ-03": {"reliability": "high", "auto_safe": True},
    "UH-01": {"reliability": "high", "auto_safe": True},
    "SE-10": {"reliability": "medium", "auto_safe": False},
    "SE-26": {"reliability": "high", "auto_safe": True},
    "SE-07": {"reliability": "high", "auto_safe": True},
    "SE-09": {"reliability": "high", "auto_safe": True},
    "SE-31": {"reliability": "medium", "auto_safe": False},
    "IM-01": {"reliability": "high", "auto_safe": True},
    "CO-01": {"reliability": "high", "auto_safe": True},
    "CV-01": {"reliability": "high", "auto_safe": True},
    "CA-01": {"reliability": "high", "auto_safe": True},
    "IO-01": {"reliability": "high", "auto_safe": True},
    "IN-01": {"reliability": "high", "auto_safe": True},
    "SE-02": {"reliability": "medium", "auto_safe": False},
    "SE-12": {"reliability": "medium", "auto_safe": False},
    "AP-C8": {"reliability": "low", "auto_safe": False},
    "AP-C18": {"reliability": "medium", "auto_safe": False},
    "AP-C19": {"reliability": "low", "auto_safe": False},
    "BANDIT-B101": {"reliability": "medium", "auto_safe": True},
    "D21-CMA": {"reliability": "medium", "auto_safe": True},
    "D21-SM": {"reliability": "medium", "auto_safe": True},
    "D35-SILENT-FALLBACK": {"reliability": "medium", "auto_safe": True},
    "D38-PATH-RESOLVE": {"reliability": "medium", "auto_safe": True},
    "HP-003": {"reliability": "medium", "auto_safe": True},
    "HP-006": {"reliability": "high", "auto_safe": True},
    "HP-GEN": {"reliability": "medium", "auto_safe": True},
    "T18-MAGIC-NUMBER": {"reliability": "medium", "auto_safe": True},
    "mutable_global": {"reliability": "medium", "auto_safe": False},
    "RUFF-UP006": {"reliability": "medium", "auto_safe": False},
    "RUFF-UP045": {"reliability": "medium", "auto_safe": False},
    "RUFF-UP037": {"reliability": "medium", "auto_safe": False},
    "RUFF-UP032": {"reliability": "high", "auto_safe": True},
    "RUFF-F541": {"reliability": "high", "auto_safe": True},
    "RUFF-F401": {"reliability": "high", "auto_safe": True},
    "RUFF-G004": {"reliability": "high", "auto_safe": True},
    "RUFF-PERF102": {"reliability": "high", "auto_safe": True},
    "RUFF-C403": {"reliability": "high", "auto_safe": True},
    "RUFF-SIM102": {"reliability": "high", "auto_safe": True},
    "RUFF-SIM103": {"reliability": "high", "auto_safe": True},
    "RUFF-I001": {"reliability": "low", "auto_safe": False},
    "RUFF-F821": {"reliability": "low", "auto_safe": False},
    "RUFF-F811": {"reliability": "low", "auto_safe": False},
    "RUFF-F841": {"reliability": "low", "auto_safe": False},
    "RUFF-S110": {"reliability": "low", "auto_safe": False},
    "RUFF-RUF013": {"reliability": "low", "auto_safe": False},
    "RUFF-RUF059": {"reliability": "low", "auto_safe": False},
    "RUFF-PLW0211": {"reliability": "low", "auto_safe": False},
    "RUFF-PLE0605": {"reliability": "low", "auto_safe": False},
    "RUFF-DTZ005": {"reliability": "low", "auto_safe": False},
    "RUFF-DTZ006": {"reliability": "low", "auto_safe": False},
    "RUFF-B023": {"reliability": "low", "auto_safe": False},
}
def _fixer_key(rule_id: str) -> str:
    return str(rule_id or "").strip().lower().replace("-", "_")
def _build_fixer_index(table: dict) -> dict[str, str]:
    return {_fixer_key(_key): _key for _key in table}
def _fixer_table_get(table: dict, index: dict, rule_id: str):
    value = table.get(rule_id)
    if value is not None:
        return value
    key = index.get(_fixer_key(rule_id))
    return table.get(key) if key is not None else None
_FIXER_RISK_INDEX: dict[str, str] = _build_fixer_index(FIXER_RISK_META)
def get_fixer_risk(rule_id: str) -> dict:
    if not isinstance(rule_id, str) or not rule_id:
        return {}
    rule_id = canonical_rule_id(rule_id)
    meta = _fixer_table_get(FIXER_RISK_META, _FIXER_RISK_INDEX, rule_id)
    if not meta:
        return {}
    return dict(meta)
FIXER_SIDE_EFFECTS: dict[str, dict[str, str | bool]] = {
    "CQ-03": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "去重字典键，不影响外部接口"},
    "UH-01": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "修正unhashable类型，不影响接口"},
    "SE-10": {"affected_files": "当前文件", "affected_callers": "哈希值消费处（缓存key/签名校验/存储对比）", "rollback_point": True, "side_effects": "弱哈希→sha256 替换，哈希输出值变更（与 SE-10 知识对齐）"},
    "SE-26": {"affected_files": "当前文件", "affected_callers": "tarfile调用处", "rollback_point": True, "side_effects": "添加filter='data'参数，行为更安全（与 SE-26 知识对齐）"},
    "SE-07": {"affected_files": "当前文件", "affected_callers": "yaml.load调用处", "rollback_point": True, "side_effects": "yaml.load→safe_load，反序列化范围缩小"},
    "SE-09": {"affected_files": "当前文件", "affected_callers": "tempfile调用处", "rollback_point": True, "side_effects": "替换不安全tempfile调用"},
    "SE-31": {"affected_files": "当前文件", "affected_callers": "cryptography API 调用处", "rollback_point": True, "side_effects": "弃用API→新API迁移，加密行为变更（与 SE-31 知识对齐）"},
    "RB-01": {"affected_files": "当前文件", "affected_callers": "函数调用处", "rollback_point": True, "side_effects": "可变默认参数→None+内部创建，行为等价"},
    "NT-01": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "None比较修正，无副作用"},
    "TY-01": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "补充类型注解，无副作用"},
    "IM-01": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "添加缺失import，无副作用"},
    "CO-01": {"affected_files": "当前文件", "affected_callers": "os.remove调用处", "rollback_point": True, "side_effects": "os.remove→安全删除替代"},
    "DB-01": {"affected_files": "当前文件", "affected_callers": "SQLite操作处", "rollback_point": False, "side_effects": "添加with语句，连接管理变更"},
    "SE-02": {"affected_files": "当前文件", "affected_callers": "subprocess调用处", "rollback_point": False, "side_effects": "shell=True→参数列表，命令构造方式变更"},
    "SE-12": {"affected_files": "当前文件", "affected_callers": "shutil调用处", "rollback_point": False, "side_effects": "添加安全校验，删除行为变更"},
    "RD-15": {"affected_files": "当前文件", "affected_callers": "except块", "rollback_point": False, "side_effects": "宽泛except处理，捕获范围变更"},
    "RD-17": {"affected_files": "当前文件", "affected_callers": "嵌套函数引用处", "rollback_point": False, "side_effects": "嵌套函数提取为模块级，闭包变量改显式传参（与 RD-17 知识对齐）"},
    "CV-01": {"affected_files": "当前文件", "affected_callers": "os.chmod调用处", "rollback_point": True, "side_effects": "宽松权限（0o777 等）收敛为最小权限（0o600/0o644），文件权限收窄（与检测器 diag_rules_runtime 的 chmod 语义对齐）"},
    "CA-01": {"affected_files": "当前文件", "affected_callers": "assert语句", "rollback_point": True, "side_effects": "assert→显式异常，运行时行为变更"},
    "RD-01": {"affected_files": "当前文件", "affected_callers": "raise语句", "rollback_point": False, "side_effects": "raise from异常链，异常传播变更"},
    "IO-01": {"affected_files": "当前文件", "affected_callers": "requests调用处", "rollback_point": True, "side_effects": "补充 timeout=N 参数，请求由永久等待变为可中断（与 IO-03 httpx/aiohttp 同族语义）"},
    "IN-01": {"affected_files": "当前文件", "affected_callers": "open()调用处", "rollback_point": True, "side_effects": "补充 encoding='utf-8' 参数，消除平台默认编码依赖；非 UTF-8 文件读取行为可能变化"},
    "SC-01": {"affected_files": "当前文件", "affected_callers": "subprocess调用处", "rollback_point": False, "side_effects": "subprocess安全化，参数构造变更"},
    "CM-01": {"affected_files": "当前文件", "affected_callers": "open()调用处", "rollback_point": True, "side_effects": "open() 包装为 with，文件句柄生命周期变更（与 CM-01 知识对齐）"},
    "RB-03": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": True, "side_effects": "open() 包装为 with，文件关闭时机变更（与 RB-03 知识对齐）"},
    "RC-01": {"affected_files": "当前文件", "affected_callers": "__del__析构处", "rollback_point": True, "side_effects": "__del__改上下文管理器，析构时机与资源释放路径变更（与 RC-01 知识对齐）"},
    "MC-01": {"affected_files": "当前文件", "affected_callers": "无", "rollback_point": False, "side_effects": "移除 __del__/改用 weakref，对象回收时机变更（与 MC-01 知识对齐）"},
    "DG-01": {"affected_files": "当前文件", "affected_callers": "dict访问处", "rollback_point": False, "side_effects": "直接访问→dict.get，返回值可能变更"},
    "RD-08": {"affected_files": "当前文件", "affected_callers": "try块", "rollback_point": True, "side_effects": "多层 try/except 重构，异常传播路径变更"},
    "EN-01": {"affected_files": "当前文件", "affected_callers": "open()调用处", "rollback_point": True, "side_effects": "补充 encoding='utf-8' 参数，消除平台默认编码依赖；非 UTF-8 文件读取行为可能变化（与 IN-01 同内核同口径）"},
    "B09": {"affected_files": "当前文件", "affected_callers": "拼接结果消费处", "rollback_point": True, "side_effects": "循环内拼接改写为 append+join，产出字符串等价"},
}
_FIXER_SIDE_EFFECT_INDEX: dict[str, str] = _build_fixer_index(
    FIXER_SIDE_EFFECTS)
_DUP_DEF_KINDS = (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
_TRY_STAR_DEF_NODES = (ast.TryStar,) if hasattr(ast, "TryStar") else ()
_TRY_DEF_NODES = (ast.Try, *_TRY_STAR_DEF_NODES)
_DUP_DECLARATION_DECORATORS = frozenset({"overload"})
_DUP_PROPERTY_ACCESSORS = frozenset({"setter", "getter", "deleter"})
def _dup_property_accessor_kind(node: ast.AST) -> str:
    name = getattr(node, "name", "")
    for dec in getattr(node, "decorator_list", ()):
        target = dec.func if isinstance(dec, ast.Call) else dec
        if (isinstance(target, ast.Attribute)
                and target.attr in _DUP_PROPERTY_ACCESSORS
                and isinstance(target.value, ast.Name)
                and target.value.id == name):
            return target.attr
    return ""
def _dup_is_declaration_only(node: ast.AST) -> bool:
    return any(
        decorator_name(dec) in _DUP_DECLARATION_DECORATORS
        for dec in getattr(node, "decorator_list", ()))
def _dup_definition_key(node: ast.AST) -> tuple[str, str] | None:
    if _dup_is_declaration_only(node):
        return None
    return node.name, _dup_property_accessor_kind(node) or "definition"
def _dup_statement_block(parent: ast.AST, child: ast.AST):
    for field in ("body", "orelse", "finalbody"):
        block = getattr(parent, field, None)
        if not isinstance(block, list):
            continue
        for index, statement in enumerate(block):
            if statement is child:
                return block, index
    return None
def _dup_try_definition_may_reach_handler(
        definition: ast.AST, try_node: ast.AST,
        parents: dict[int, ast.AST]) -> bool:
    path: list[tuple[ast.AST, ast.AST]] = []
    current = definition
    while True:
        parent = parents.get(id(current))
        if parent is None:
            return False
        path.append((parent, current))
        if parent is try_node:
            if not any(statement is current for statement in try_node.body):
                return False
            break
        current = parent
    if any(
            isinstance(parent, (ast.With, ast.AsyncWith))
            or (isinstance(parent, (ast.For, ast.AsyncFor, ast.While))
                and any(statement is child for statement in parent.body))
            for parent, child in path):
        return True
    ancestor = try_node
    while True:
        parent = parents.get(id(ancestor))
        if parent is None:
            break
        if (isinstance(parent, (ast.For, ast.AsyncFor, ast.While))
                and any(statement is ancestor for statement in parent.body)):
            return True
        ancestor = parent
    for parent, child in path:
        located = _dup_statement_block(parent, child)
        if located is None:
            continue
        block, index = located
        if index + 1 < len(block):
            return True
    return False
def _dup_constraints_compatible(
        left: tuple, right: tuple, left_node: ast.AST, right_node: ast.AST,
        parents: dict[int, ast.AST],
        try_nodes: dict[int, ast.AST]) -> bool:
    right_branches = dict(right)
    for node_id, branch in left:
        other_branch = right_branches.get(node_id)
        if other_branch is None or other_branch == branch:
            continue
        branches = {branch, other_branch}
        if ("try_normal" in branches
                and any(item.startswith("handler_") for item in branches)):
            normal_node = left_node if branch == "try_normal" else right_node
            if _dup_try_definition_may_reach_handler(
                    normal_node, try_nodes[node_id], parents):
                continue
        if (all(item.startswith("handler_") for item in branches)
                and isinstance(try_nodes[node_id], _TRY_STAR_DEF_NODES)):
            continue
        return False
    return True
def _dup_definition_groups(tree: ast.AST) -> list[list]:
    groups: list[list] = []
    def visit_scope(body: list) -> None:
        entries: list = []
        groups.append(entries)
        visit_statements(body, (), entries)
    def visit_statements(statements: list, constraints: tuple,
                         entries: list) -> None:
        for stmt in statements:
            if isinstance(stmt, _DUP_DEF_KINDS):
                key = _dup_definition_key(stmt)
                if key is not None:
                    entries.append((key, constraints, stmt))
                visit_scope(stmt.body)
                continue
            if isinstance(stmt, ast.If):
                visit_statements(
                    stmt.body, constraints + ((id(stmt), "if"),), entries)
                visit_statements(
                    stmt.orelse, constraints + ((id(stmt), "else"),), entries)
                continue
            if isinstance(stmt, (ast.For, ast.AsyncFor, ast.While)):
                branch = constraints + ((id(stmt), "loop"),)
                visit_statements(stmt.body, branch, entries)
                visit_statements(stmt.orelse, branch, entries)
                continue
            if isinstance(stmt, (ast.With, ast.AsyncWith)):
                visit_statements(stmt.body, constraints, entries)
                continue
            if isinstance(stmt, _TRY_DEF_NODES):
                normal = constraints + ((id(stmt), "try_normal"),)
                visit_statements(stmt.body, normal, entries)
                visit_statements(stmt.orelse, normal, entries)
                for index, handler in enumerate(stmt.handlers):
                    branch = constraints + ((id(stmt), f"handler_{index}"),)
                    visit_statements(handler.body, branch, entries)
                visit_statements(stmt.finalbody, constraints, entries)
                continue
            if isinstance(stmt, ast.Match):
                for index, case in enumerate(stmt.cases):
                    branch = constraints + ((id(stmt), f"case_{index}"),)
                    visit_statements(case.body, branch, entries)
    visit_scope(tree.body)
    return groups
def _dup_definition_in_tree(tree: ast.AST) -> bool:
    parents = {
        id(child): parent
        for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    try_nodes = {
        id(node): node for node in walk_nodes(tree)
        if isinstance(node, _TRY_DEF_NODES)
    }
    for entries in _dup_definition_groups(tree):
        for index, (key, constraints, node) in enumerate(entries):
            for other_key, other_constraints, other_node in entries[index + 1:]:
                if (key == other_key and _dup_constraints_compatible(
                        constraints, other_constraints, node, other_node,
                        parents, try_nodes)):
                    return True
    return False
def _dup_definition_flat(code: str) -> bool:
    names = re.findall(r"^(?:async[ \t]+def|def|class)\s+(\w+)", code,
                        re.MULTILINE)
    return len(names) != len(set(names))
def _blacklist_has_duplicate_definition(code: str,
                                        tree: ast.AST | None) -> bool:
    if tree is None:
        return _dup_definition_flat(code)
    return _dup_definition_in_tree(tree)
def _skip_space_and_comments(code: str, idx: int) -> int:
    length = len(code)
    while idx < length:
        char = code[idx]
        if char.isspace():
            idx += 1
            continue
        if char == "\\" and idx + 1 < length and code[idx + 1] in "\r\n":
            idx += 2
            continue
        if char != "#":
            break
        newline = code.find("\n", idx + 1)
        if newline < 0:
            return length
        idx = newline + 1
    return idx
def _star_opens_vararg(code: str, idx: int) -> bool:
    idx = _skip_space_and_comments(code, idx)
    if idx >= len(code):
        return False
    return code[idx] not in ",)"
def _skip_quoted_param_text(code: str, idx: int) -> int:
    quote = code[idx]
    idx += 1
    while idx < len(code):
        if code[idx] == "\\":
            idx += 2
            continue
        if code[idx] == quote:
            return idx + 1
        idx += 1
    return idx
def _params_accept_varargs(code: str, start: int) -> bool:
    depth = 1
    prev = "("
    idx = start
    while idx < len(code) and depth:
        char = code[idx]
        if char in ("'", '"'):
            idx = _skip_quoted_param_text(code, idx)
            continue
        skipped = _skip_space_and_comments(code, idx)
        if skipped != idx:
            idx = skipped
            continue
        if char in "([{":
            depth += 1
            prev = char
        elif char in ")]}":
            depth -= 1
        else:
            if (char == "*" and depth == 1 and prev in "(,"
                    and _star_opens_vararg(code, idx + 1)):
                return True
            prev = char
        idx += 1
    return False
def _init_signature_missing_varargs(tree: ast.AST) -> bool:
    return any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == "__init__"
        and node.args.vararg is None
        and node.args.kwarg is None
        for node in walk_nodes(tree)
    )
def _blacklist_init_signature_hit_text(code: str) -> bool:
    for match in re.finditer(r"def\s+__init__\s*\(", code):
        if not _params_accept_varargs(code, match.end()):
            return True
    return False
def _blacklist_init_signature_hit(code: str,
                                  tree: ast.AST | None) -> bool:
    if tree is None:
        return _blacklist_init_signature_hit_text(code)
    return _init_signature_missing_varargs(tree)
def _blacklist_getattr_hit(code: str, tree: ast.AST | None) -> bool:
    if tree is None:
        return bool(re.search(r"\bdef\s+__getattr__\s*\(", code))
    return any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == "__getattr__"
        for node in walk_nodes(tree)
    )
def _is_all_reference(node: ast.AST, name_only: bool = False) -> bool:
    return ((isinstance(node, ast.Name) and node.id == "__all__")
            or (not name_only and isinstance(node, ast.Attribute)
                and node.attr == "__all__"))
def _all_assignment_target_hit(node: ast.AST,
                               name_only: bool = False) -> bool:
    if _is_all_reference(node, name_only):
        return True
    if isinstance(node, ast.Starred):
        return _all_assignment_target_hit(node.value, name_only)
    if isinstance(node, ast.Subscript):
        return _all_assignment_target_hit(node.value, name_only)
    if isinstance(node, (ast.Tuple, ast.List)):
        return any(_all_assignment_target_hit(item, name_only)
                   for item in node.elts)
    return False
_ALL_MUTATOR_NAMES = frozenset({
    "append", "extend", "remove", "insert", "pop", "clear", "sort", "reverse",
})
_ALL_MUTATOR_PATTERN = "|".join(
    re.escape(name) for name in sorted(_ALL_MUTATOR_NAMES)
)
def _all_assignment_targets(node: ast.AST) -> tuple:
    if isinstance(node, ast.Assign):
        return tuple(node.targets)
    if isinstance(node, ast.AnnAssign):
        return (node.target,) if node.value is not None else ()
    if isinstance(node, ast.AugAssign):
        return (node.target,)
    if isinstance(node, ast.NamedExpr):
        return (node.target,)
    if isinstance(node, ast.Delete):
        return tuple(node.targets)
    return ()
def _all_binding_target_hit(node: ast.AST,
                            name_only: bool = False) -> bool:
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _all_assignment_target_hit(node.target, name_only)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return any(
            item.optional_vars is not None
            and _all_assignment_target_hit(item.optional_vars, name_only)
            for item in node.items)
    if isinstance(node, ast.ExceptHandler):
        return node.name == "__all__"
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        return any(
            (alias.asname or alias.name.split(".", 1)[0]) == "__all__"
            for alias in node.names)
    if isinstance(node, _DUP_DEF_KINDS):
        return node.name == "__all__"
    if isinstance(node, (ast.MatchAs, ast.MatchStar)):
        return node.name == "__all__"
    if isinstance(node, ast.MatchMapping):
        return node.rest == "__all__"
    return False
def _all_mutation_node_hit(node: ast.AST,
                           name_only: bool = False) -> bool:
    if _all_binding_target_hit(node, name_only):
        return True
    targets = _all_assignment_targets(node)
    if any(_all_assignment_target_hit(target, name_only)
           for target in targets):
        return True
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _ALL_MUTATOR_NAMES
            and _is_all_reference(node.func.value, name_only))
def _all_attribute_target_hit(node: ast.AST) -> bool:
    if isinstance(node, ast.Attribute):
        return node.attr == "__all__"
    if isinstance(node, ast.Starred):
        return _all_attribute_target_hit(node.value)
    if isinstance(node, ast.Subscript):
        return _all_attribute_target_hit(node.value)
    if isinstance(node, (ast.Tuple, ast.List)):
        return any(_all_attribute_target_hit(item) for item in node.elts)
    return False

def _all_attribute_mutation_node_hit(node: ast.AST) -> bool:
    if any(_all_attribute_target_hit(target)
           for target in _all_assignment_targets(node)):
        return True
    if (isinstance(node, (ast.For, ast.AsyncFor))
            and _all_attribute_target_hit(node.target)):
        return True
    if isinstance(node, (ast.With, ast.AsyncWith)) and any(
            item.optional_vars is not None
            and _all_attribute_target_hit(item.optional_vars)
            for item in node.items):
        return True
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _ALL_MUTATOR_NAMES
            and isinstance(node.func.value, ast.Attribute)
            and node.func.value.attr == "__all__")

def _function_all_declaration(scope: ast.AST) -> str:
    for node in iter_scope_nodes(scope):
        if isinstance(node, ast.Global) and "__all__" in node.names:
            return "global"
        if isinstance(node, ast.Nonlocal) and "__all__" in node.names:
            return "nonlocal"
    return ""
def _function_all_binding(scope: ast.AST) -> bool:
    if "__all__" in collect_param_names(scope):
        return True
    for node in iter_scope_nodes(scope):
        if (isinstance(node, ast.AnnAssign)
                and _all_name_target_hit(node.target)):
            return True
        if any(_all_name_target_hit(target)
               for target in _all_assignment_targets(node)):
            return True
        if _all_binding_target_hit(node, name_only=True):
            return True
    return False
def _comprehension_outer_iter(scope: ast.AST, child: ast.AST,
                              below: ast.AST | None) -> bool:
    return bool(
        isinstance(child, ast.comprehension) and scope.generators
        and child is scope.generators[0] and below is child.iter)
def _all_name_resolves_to_module(node: ast.AST, parents: dict) -> bool:
    current = parents.get(id(node))
    child = node
    below = None
    crossed_function = False
    while current is not None:
        if isinstance(current, COMP_SCOPE_NODES):
            if (not _comprehension_outer_iter(current, child, below)
                    and "__all__" in comp_target_names(current)):
                return False
        elif isinstance(current, (*FUNC_NODE_TYPES, ast.Lambda)):
            crossed_function = True
            declaration = _function_all_declaration(current)
            if declaration == "global":
                return True
            if (declaration != "nonlocal"
                    and _function_all_binding(current)):
                return False
        elif isinstance(current, ast.ClassDef):
            if not crossed_function:
                return False
        elif isinstance(current, ast.Module):
            return True
        below = child
        child = current
        current = parents.get(id(current))
    return False
def _lexical_all_mutation_in_tree(tree: ast.AST) -> bool:
    parents = {
        id(child): parent
        for parent in walk_nodes(tree)
        for child in ast.iter_child_nodes(parent)
    }
    for node in walk_nodes(tree):
        if _all_attribute_mutation_node_hit(node):
            return True
        if (_all_mutation_node_hit(node, name_only=True)
                and _all_name_resolves_to_module(node, parents)):
            return True
    return False
def _module_scope_all_mutation_in_tree(tree: ast.AST) -> bool:
    return (_lexical_all_mutation_in_tree(tree)
            or _class_execution_all_mutation_in_tree(tree))
def _blacklist_all_hit(code: str, tree: ast.AST | None) -> bool:
    if tree is None:
        return bool(
            re.search(
                r"(?<![A-Za-z0-9_])__all__(?:\s*:\s*[^=\n]+)?\s*\+?=(?!=)", code)
            or re.search(
                rf"(?<![A-Za-z0-9_])__all__\."
                rf"(?:{_ALL_MUTATOR_PATTERN})\b", code))
    return _module_scope_all_mutation_in_tree(tree)
def _function_scope_import_in_tree(tree: ast.AST) -> bool:
    stack: list[tuple[ast.AST, bool]] = [(tree, False)]
    while stack:
        node, in_function = stack.pop()
        if in_function and isinstance(node, (ast.Import, ast.ImportFrom)):
            return True
        child_in_function = in_function or isinstance(
            node, (ast.FunctionDef, ast.AsyncFunctionDef))
        stack.extend(
            (child, child_in_function) for child in ast.iter_child_nodes(node))
    return False
def _blacklist_function_import_hit_text(code: str) -> bool:
    return bool(re.search(r"^[ \t]+(?:import|from)\s", code, re.MULTILINE))
def _blacklist_function_import_hit(code: str,
                                    tree: ast.AST | None) -> bool:
    if tree is None:
        return _blacklist_function_import_hit_text(code)
    return _function_scope_import_in_tree(tree)
_MODULE_SCOPE_BOUNDARY_NODES = (*_DUP_DEF_KINDS, ast.Lambda)
def _definition_time_children(node: ast.AST) -> list:
    if isinstance(node, ast.ClassDef):
        return [*node.decorator_list, *node.bases, *node.keywords]
    if isinstance(node, FUNC_NODE_TYPES):
        args = node.args
        children = [*node.decorator_list, *args.defaults]
        children.extend(d for d in args.kw_defaults if d is not None)
        children.extend((*args.posonlyargs, *args.args, *args.kwonlyargs))
        if args.vararg is not None:
            children.append(args.vararg)
        if args.kwarg is not None:
            children.append(args.kwarg)
        if node.returns is not None:
            children.append(node.returns)
        return children
    if isinstance(node, ast.Lambda):
        children = list(node.args.defaults)
        children.extend(d for d in node.args.kw_defaults if d is not None)
        return children
    return []
def _iter_module_scope_nodes(tree: ast.AST):
    stack = [tree]
    while stack:
        node = stack.pop()
        yield node
        if isinstance(node, _MODULE_SCOPE_BOUNDARY_NODES):
            stack.extend(_definition_time_children(node))
            continue
        stack.extend(ast.iter_child_nodes(node))
def _class_scope_tree(node: ast.ClassDef) -> ast.Module:
    return ast.Module(body=node.body, type_ignores=[])
def _iter_execution_classes(tree: ast.AST):
    for node in walk_nodes(tree):
        if isinstance(node, ast.ClassDef):
            yield node
def _class_global_names(node: ast.ClassDef) -> set[str]:
    return {
        name
        for child in _iter_module_scope_nodes(_class_scope_tree(node))
        if isinstance(child, ast.Global)
        for name in child.names
    }
def _all_name_target_hit(node: ast.AST) -> bool:
    if isinstance(node, ast.Name):
        return node.id == "__all__"
    if isinstance(node, ast.Starred):
        return _all_name_target_hit(node.value)
    if isinstance(node, (ast.Tuple, ast.List)):
        return any(_all_name_target_hit(item) for item in node.elts)
    return False

def _all_subscript_target_hit(node: ast.AST) -> bool:
    if isinstance(node, ast.Subscript):
        return _all_assignment_target_hit(node.value, name_only=True)
    if isinstance(node, ast.Starred):
        return _all_subscript_target_hit(node.value)
    if isinstance(node, (ast.Tuple, ast.List)):
        return any(_all_subscript_target_hit(item) for item in node.elts)
    return False

def _class_unqualified_all_mutation_node_hit(node: ast.AST) -> bool:
    if (isinstance(node, ast.AugAssign)
            and _all_assignment_target_hit(node.target, name_only=True)):
        return True
    if any(_all_subscript_target_hit(target)
           for target in _all_assignment_targets(node)):
        return True
    if (isinstance(node, (ast.For, ast.AsyncFor))
            and _all_subscript_target_hit(node.target)):
        return True
    if (isinstance(node, (ast.With, ast.AsyncWith)) and any(
            item.optional_vars is not None
            and _all_subscript_target_hit(item.optional_vars)
            for item in node.items)):
        return True
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in _ALL_MUTATOR_NAMES
            and _is_all_reference(node.func.value, name_only=True))

def _class_all_binding(node: ast.AST) -> bool:
    if isinstance(node, ast.Delete):
        return False
    if any(_all_name_target_hit(target)
           for target in _all_assignment_targets(node)):
        return True
    if isinstance(node, (ast.For, ast.AsyncFor)):
        return _all_name_target_hit(node.target)
    if isinstance(node, (ast.With, ast.AsyncWith)):
        return any(item.optional_vars is not None
                   and _all_name_target_hit(item.optional_vars)
                   for item in node.items)
    return _all_binding_target_hit(node, name_only=True)

def _class_all_unbinding(node: ast.AST) -> bool:
    return (isinstance(node, ast.Delete)
            and any(_all_name_target_hit(target) for target in node.targets))

def _all_name_is_comprehension_local(node: ast.AST, parents: dict) -> bool:
    current = parents.get(id(node))
    child = node
    below = None
    while current is not None:
        if isinstance(current, COMP_SCOPE_NODES):
            if (not _comprehension_outer_iter(current, child, below)
                    and "__all__" in comp_target_names(current)):
                return True
        elif isinstance(current, (*FUNC_NODE_TYPES, ast.Lambda,
                                  ast.ClassDef, ast.Module)):
            break
        below = child
        child = current
        current = parents.get(id(current))
    return False
def _class_all_expr_hit(node: ast.AST, bound: bool) -> bool:
    if bound:
        return False
    parents = {
        id(child): parent
        for parent in walk_nodes(node)
        for child in ast.iter_child_nodes(parent)
    }
    for child in _iter_module_scope_nodes(node):
        if not _class_unqualified_all_mutation_node_hit(child):
            continue
        if not _all_name_is_comprehension_local(child, parents):
            return True
    return False

def _analyze_class_all_statements(statements: list,
                                  bound: bool) -> tuple[bool, bool]:
    for statement in statements:
        hit, bound = _analyze_class_all_statement(statement, bound)
        if hit:
            return True, bound
    return False, bound

def _analyze_class_all_statement(node: ast.AST,
                                 bound: bool) -> tuple[bool, bool]:
    if isinstance(node, ast.If):
        hit = _class_all_expr_hit(node.test, bound)
        body_hit, body_bound = _analyze_class_all_statements(node.body, bound)
        else_hit, else_bound = _analyze_class_all_statements(node.orelse, bound)
        return hit or body_hit or else_hit, body_bound and else_bound
    if isinstance(node, (ast.For, ast.AsyncFor)):
        hit = (_class_all_expr_hit(node.iter, bound)
               or _class_all_expr_hit(node.target, bound)
               or (not bound
                   and _class_unqualified_all_mutation_node_hit(node)))
        body_bound = True if _all_name_target_hit(node.target) else bound
        body_hit, _ = _analyze_class_all_statements(node.body, body_bound)
        else_hit, _ = _analyze_class_all_statements(node.orelse, bound)
        return hit or body_hit or else_hit, bound
    if isinstance(node, ast.While):
        hit = _class_all_expr_hit(node.test, bound)
        body_hit, _ = _analyze_class_all_statements(node.body, bound)
        else_hit, _ = _analyze_class_all_statements(node.orelse, bound)
        return hit or body_hit or else_hit, bound
    if isinstance(node, (ast.With, ast.AsyncWith)):
        hit = False
        for item in node.items:
            hit = hit or _class_all_expr_hit(item.context_expr, bound)
            if item.optional_vars is not None:
                hit = (hit or _class_all_expr_hit(item.optional_vars, bound)
                       or (not bound
                           and _all_subscript_target_hit(item.optional_vars)))
                if _all_name_target_hit(item.optional_vars):
                    bound = True
        body_hit, body_bound = _analyze_class_all_statements(node.body, bound)
        return hit or body_hit, body_bound
    if isinstance(node, _TRY_DEF_NODES):
        hit, normal_bound = _analyze_class_all_statements(node.body, bound)
        else_hit, normal_bound = _analyze_class_all_statements(
            node.orelse, normal_bound)
        hit = hit or else_hit
        handler_bounds = []
        for handler in node.handlers:
            if handler.type is not None:
                hit = hit or _class_all_expr_hit(handler.type, bound)
            handler_bound = True if handler.name == "__all__" else bound
            handler_hit, handler_bound = _analyze_class_all_statements(
                handler.body, handler_bound)
            hit = hit or handler_hit
            if handler.name == "__all__":
                handler_bound = False
            handler_bounds.append(handler_bound)
        normal_bound = normal_bound and all(handler_bounds)
        final_hit, final_bound = _analyze_class_all_statements(
            node.finalbody, bound)
        return hit or final_hit, final_bound if node.finalbody else normal_bound
    if isinstance(node, ast.Match):
        hit = _class_all_expr_hit(node.subject, bound)
        bound_after = True
        has_default = False
        for case in node.cases:
            case_bound = bound or _all_binding_target_hit(
                case.pattern, name_only=True)
            if case.guard is not None:
                hit = hit or _class_all_expr_hit(case.guard, case_bound)
            case_hit, case_bound = _analyze_class_all_statements(
                case.body, case_bound)
            hit = hit or case_hit
            bound_after = bound_after and case_bound
            if (isinstance(case.pattern, ast.MatchAs)
                    and case.pattern.pattern is None and case.guard is None):
                has_default = True
        if not has_default:
            bound_after = bound_after and bound
        return hit, bound_after
    hit = _class_all_expr_hit(node, bound)
    if _class_all_unbinding(node):
        bound = False
    elif _class_all_binding(node):
        bound = True
    return hit, bound

def _class_execution_all_mutation_in_tree(tree: ast.AST) -> bool:
    for class_node in _iter_execution_classes(tree):
        class_tree = _class_scope_tree(class_node)
        if any(_all_attribute_mutation_node_hit(node)
               for node in _iter_module_scope_nodes(class_tree)):
            return True
        if "__all__" in _class_global_names(class_node):
            if any(_all_mutation_node_hit(node, name_only=True)
                   for node in _iter_module_scope_nodes(class_tree)):
                return True
            continue
        hit, _bound = _analyze_class_all_statements(class_node.body, False)
        if hit:
            return True
    return False
def _delete_target_names(node: ast.AST) -> set[str]:
    if isinstance(node, ast.Name):
        return {node.id}
    if isinstance(node, ast.Starred):
        return _delete_target_names(node.value)
    if isinstance(node, ast.Subscript):
        return _delete_target_names(node.value)
    if isinstance(node, (ast.Tuple, ast.List)):
        return set().union(*(_delete_target_names(item) for item in node.elts))
    return set()
def _class_global_delete_in_tree(tree: ast.AST) -> bool:
    for class_node in _iter_execution_classes(tree):
        global_names = _class_global_names(class_node)
        if not global_names:
            continue
        for node in _iter_module_scope_nodes(_class_scope_tree(class_node)):
            if (isinstance(node, ast.Delete)
                    and any(_delete_target_names(target) & global_names
                            for target in node.targets)):
                return True
    return False
def _module_scope_delete_in_tree(tree: ast.AST) -> bool:
    return (any(isinstance(node, ast.Delete)
                for node in _iter_module_scope_nodes(tree))
            or _class_global_delete_in_tree(tree))
def _blacklist_top_level_delete_hit(code: str,
                                    tree: ast.AST | None) -> bool:
    if tree is None:
        return bool(re.search(r"^del\s+\w+", code, re.MULTILINE))
    return _module_scope_delete_in_tree(tree)
_GLOBALS_MUTATOR_NAMES = frozenset({
    "clear", "pop", "popitem", "setdefault", "update",
    "__setitem__", "__delitem__",
})
_GLOBALS_MUTATOR_PATTERN = "|".join(
    re.escape(name) for name in sorted(_GLOBALS_MUTATOR_NAMES)
)
def _globals_exec_change_in_tree(tree: ast.AST) -> bool:
    for node in walk_nodes(tree):
        if (isinstance(node, ast.Subscript)
                and isinstance(node.ctx, (ast.Store, ast.Del))
                and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and node.value.func.id == "globals"
                and not node.value.args and not node.value.keywords):
            return True
        if isinstance(node, ast.Call):
            func = node.func
            if ((isinstance(func, ast.Name) and func.id in {"exec", "eval"})
                    or (isinstance(func, ast.Attribute)
                        and func.attr in {"exec", "eval"})):
                return True
            if (isinstance(func, ast.Attribute)
                    and func.attr in _GLOBALS_MUTATOR_NAMES
                    and isinstance(func.value, ast.Call)
                    and isinstance(func.value.func, ast.Name)
                    and func.value.func.id == "globals"
                    and not func.value.args and not func.value.keywords):
                return True
    return False
def _blacklist_globals_exec_hit(code: str,
                                tree: ast.AST | None) -> bool:
    if tree is None:
        return bool(
            re.search(r"\bglobals\s*\(\s*\)\s*\[", code)
            or re.search(
                rf"\bglobals\s*\(\s*\)\s*\.\s*"
                rf"(?:{_GLOBALS_MUTATOR_PATTERN})\b", code)
            or re.search(r"\bexec\s*\(", code)
            or re.search(r"\beval\s*\(", code))
    return _globals_exec_change_in_tree(tree)
def _parse_blacklist_code(code: str) -> tuple[ast.AST | None, Exception | None]:
    try:
        return ast.parse(code), None
    except PARSE_DEGRADE_EXC as exc:
        log_swallowed(__name__, exc,
                      context=f'_parse_blacklist_code:{type(exc).__name__}')
        return None, exc
_BLACKLIST_SPEC: tuple[
    tuple[str, str, Callable[[str, ast.AST | None], bool]], ...] = (
    (
        "__getattr__",
        "禁止修改 __getattr__ 方法（影响所有属性访问，极易引入无限递归）",
        _blacklist_getattr_hit,
    ),
    (
        "__all__",
        "禁止修改 __all__ 列表（影响模块导出接口，可能导致外部依赖断裂）",
        _blacklist_all_hit,
    ),
    (
        "__init__signature",
        "禁止修改 __init__ 方法签名（影响所有实例化调用，破坏向后兼容）",
        _blacklist_init_signature_hit,
    ),
    (
        "function_level_import",
        "禁止在函数体内添加/删除 import 语句（影响模块加载顺序，可能引入循环导入）",
        _blacklist_function_import_hit,
    ),
    (
        "top_level_add_delete",
        "禁止在模块顶层删除定义（删除会破坏外部引用；同层新增定义由重名检查覆盖）",
        _blacklist_top_level_delete_hit,
    ),
    (
        "globals_exec_change",
        "禁止修改 globals() 调用或 exec/eval 语句（安全风险极高，可能引入任意代码执行）",
        _blacklist_globals_exec_hit,
    ),
    (
        "duplicate_definition",
        "禁止创建与已有定义同名的函数/类（覆盖已有定义，导致功能丢失）",
        _blacklist_has_duplicate_definition,
    ),
)
FIXER_BLACKLIST: dict[str, str] = {
    pattern: reason for pattern, reason, _ in _BLACKLIST_SPEC
}
_BLACKLIST_MATCHERS: tuple[
    tuple[str, Callable[[str, ast.AST | None], bool]], ...] = tuple(
        (pattern, matcher) for pattern, _, matcher in _BLACKLIST_SPEC
)
def check_fixer_blacklist(
        code_to_write: str = _DEFAULT_CODE_TO_WRITE) -> tuple[bool, str]:
    if not code_to_write or not isinstance(code_to_write, str):
        return False, ""
    tree, parse_error = _parse_blacklist_code(code_to_write)
    if parse_error is not None:
        log_swallowed(
            __name__, parse_error,
            context="check_fixer_blacklist:AST解析失败,各检测器退回保守文本口径")
    for pattern, matcher in _BLACKLIST_MATCHERS:
        if matcher(code_to_write, tree):
            return True, f"黑名单命中: {FIXER_BLACKLIST[pattern]}"
    return False, ""
def _unknown_rule_precheck_result() -> dict:
    return {
        "rule_id": "", "q1_what_changes": _UNDECLARED,
        "q2_who_affected": _UNDECLARED,
        "q3_rollback_ready": False, "side_effects": _UNDECLARED,
        "reliability": "unknown", "auto_safe": False,
        "blacklist_check": "unknown_rule", "approved": False,
    }
def _assemble_precheck_result(rule_id: str, risk: dict,
                              side_effects: dict) -> dict:
    auto_safe = bool(risk.get("auto_safe", False))
    return {
        "rule_id": rule_id,
        "q1_what_changes": side_effects.get("affected_files", "当前文件"),
        "q2_who_affected": side_effects.get("affected_callers", "未知"),
        "q3_rollback_ready": bool(side_effects.get("rollback_point", auto_safe)),
        "side_effects": side_effects.get("side_effects", _UNDECLARED),
        "reliability": risk.get("reliability", "unknown"),
        "auto_safe": auto_safe,
        "blacklist_check": "passed",
        "approved": False,
    }
def _declared_evidence(value: object, placeholders: set[str]) -> bool:
    if not isinstance(value, str):
        return False
    text = value.strip()
    return bool(text) and text not in placeholders
def _apply_approval_decision(result: dict) -> None:
    evidence_complete = all((
        _declared_evidence(result["q1_what_changes"], {"", _UNDECLARED}),
        _declared_evidence(
            result["q2_who_affected"], {"", "未知", _UNDECLARED}),
        _declared_evidence(result["side_effects"], {"", _UNDECLARED}),
    ))
    result["approved"] = bool(
        result["auto_safe"] and result["q3_rollback_ready"]
        and evidence_complete)
    if not result["approved"]:
        result["blacklist_check"] = "needs_manual_review"
def formalize_fix_precheck(
        rule_id: str, code_to_write: str = _DEFAULT_CODE_TO_WRITE) -> dict:
    _t0 = time.monotonic()
    def _trace(outcome: str, res: dict) -> dict:
        write_module_run(
            _MODULE_NAME, "formalize_fix_precheck",
            duration_ms=(time.monotonic() - _t0) * 1000.0,
            outcome=outcome, rule_id=str(res.get("rule_id", "")),
            reliability=str(res.get("reliability", "unknown")),
            auto_safe=bool(res.get("auto_safe", False)),
            blacklist_check=str(res.get("blacklist_check", "")),
            approved=bool(res.get("approved", False)))
        return res
    if not isinstance(rule_id, str) or not rule_id.strip():
        return _trace("unknown_rule", _unknown_rule_precheck_result())
    _canonical = canonical_rule_id(rule_id)
    risk = get_fixer_risk(_canonical)
    side_effects = _fixer_table_get(
        FIXER_SIDE_EFFECTS, _FIXER_SIDE_EFFECT_INDEX, _canonical) or {}
    result = _assemble_precheck_result(
        _canonical or rule_id, risk, side_effects)
    hit, reason = check_fixer_blacklist(code_to_write)
    if hit:
        result["blacklist_check"] = f"blocked: {reason}"
        return _trace("blacklist_blocked", result)
    _apply_approval_decision(result)
    return _trace("ok", result)
_ALWAYS_ROUTED_CONCLUSIONS = ("confirmed", "investigated")
_LIKELY_ROUTE_CONFIDENCE = 0.75
def _entry_should_process(conclusion: object, adjusted_conf: float,
                          sources: list) -> bool:
    if conclusion in _ALWAYS_ROUTED_CONCLUSIONS:
        return True
    if conclusion == "likely":
        return (adjusted_conf >= _LIKELY_ROUTE_CONFIDENCE
                or len(sources) >= 2)
    return False
def _route_finding(finding: dict, locator: str, sources: list) -> dict:
    file_path, line_val = _finding_file_line(finding, None, locator)
    return {
        "rule_id": str_or(
            finding.get("rule_id") or finding.get("rule_family")
            or finding.get("rule") or finding.get("rule_applied"), ""),
        "file": file_path,
        "line": line_val,
        "severity": (str_or(finding.get("severity"), "")
                     or _DEFAULT_SEVERITY),
        "message": str_or(
            finding.get("message") or finding.get("sample_message"), ""),
        "locator": locator,
        "finding_id": str_or(finding.get("finding_id"), ""),
        "sources": list(sources),
    }
def _expand_entry_findings(entry: dict, locator: str, sources: list) -> list:
    entry_findings = _dict_items(entry.get("findings"))
    sample = entry.get("sample_finding")
    if not entry_findings and isinstance(sample, dict):
        entry_findings = [sample]
    expanded = []
    for f in entry_findings:
        if not f:
            logger.warning(
                "[TreatmentStep] CV 路由跳过空 finding: locator=%s", locator)
            continue
        expanded.append(_route_finding(f, locator, sources))
    return expanded
def _collect_confirmed_findings(cv_report: dict) -> list:
    confirmed_findings = []
    direct = cv_report.get("confirmed_findings")
    if isinstance(direct, list):
        for finding in _dict_items(direct):
            if not finding:
                logger.warning("[TreatmentStep] CV 路由跳过空 confirmed finding")
                continue
            locator = str_or(finding.get("locator"), "")
            confirmed_findings.append(_route_finding(
                finding, locator, normalize_sources(finding.get("sources"))))
        return confirmed_findings
    for entry in _dict_items(cv_report.get("findings_index")):
        locator = str_or(entry.get("locator"), "")
        sources = normalize_sources(entry.get("sources"))
        adjusted_conf = safe_float(entry.get(FIELD_ADJUSTED_CONFIDENCE))
        conclusion = str_or(entry.get("conclusion", "")).strip().lower()
        if not _entry_should_process(conclusion, adjusted_conf, sources):
            continue
        confirmed_findings.extend(
            _expand_entry_findings(entry, locator, sources))
    return confirmed_findings
def _dry_route_detail(finding: dict) -> dict:
    _sources = finding.get("sources")
    return {
        "rule_id": finding.get("rule_id", ""),
        "file": finding.get("file", ""),
        "line": finding.get("line", 0),
        "severity": finding.get("severity", _DEFAULT_SEVERITY),
        "locator": finding.get("locator", ""),
        "sources": list(_sources) if isinstance(_sources, list) else [],
        "message": finding.get("message", ""),
        "status": "dry_run",
        "strategy": "manual_ai",
        "has_fixer": False,
        "ai_action": "AI 审核并手动修复，再验证",
    }
def build_dry_route_report(cv_report: dict) -> dict:
    cv_report = cv_report if isinstance(cv_report, dict) else {}
    details = [_dry_route_detail(cf)
               for cf in _collect_confirmed_findings(cv_report)]
    return {
        "summary": {"total_confirmed": len(details), "total_fixable": 0},
        "details": details,
        "fix_coverage": {"covered": 0, "total": len(details)},
    }
_RULE_LINE_PATTERNS: dict[str, tuple[str, ...]] = {
    "SN-04": ("except", "return"),
    "SL-06": ("__init__",),
    "TY-01": ("type:", "TypeVar", "->"),
    "SE-20": ("try", "except"),
    "RUFF-PERF102": ("for ", "while "),
}
_SNIPPET_KEYWORD_HINTS: tuple[str, ...] = (
    "logger.debug", "_log.debug", "except", "pass", "import", "return",
)
def _search_current_or_window(lines: list[str], line: int,
                              patterns: list[str]) -> int:
    if 0 < line <= len(lines) and any(p in lines[line - 1] for p in patterns):
        return line
    return _search_window_first(lines, line, patterns)
def _search_window_first(lines: list[str], line: int,
                         patterns: list[str]) -> int:
    n = len(lines)
    search_start = max(0, line - 21)
    search_end = min(n, line + 20) if line > 0 else min(n, 50)
    for i in range(search_start, search_end):
        if any(p in lines[i] for p in patterns):
            return i + 1
    return -1
def _locate_nearest_line(lines: list[str], orig_line: int,
                         match_fn: Callable[[str], bool]) -> int:
    _best_i, _best_dist = -1, float('inf')
    for i in range(len(lines)):
        if match_fn(lines[i]):
            _dist = abs((i + 1) - orig_line)
            if _dist < _best_dist:
                _best_dist = _dist
                _best_i = i
    return _best_i + 1 if _best_i >= 0 else -1
def _locate_snippet_line(lines: list[str], code_snippet: str,
                         orig_line: int) -> int:
    _cs = code_snippet.strip()
    _first_line = _cs.split("\n", 1)[0].strip()[:40]
    if len(_first_line) < 4:
        return -1
    if orig_line <= 0:
        matches = [i + 1 for i, _ln in enumerate(lines)
                   if _first_line in _ln]
        return matches[0] if len(matches) == 1 else -1
    return _locate_nearest_line(
        lines, orig_line, lambda _ln: _first_line in _ln)
def _build_line_patterns(rule_id: str, code_snippet: str) -> list[str]:
    patterns = list(_RULE_LINE_PATTERNS.get(rule_id, ()))
    if not patterns:
        canonical = canonical_rule_id(rule_id)
        if canonical and canonical != rule_id:
            patterns = list(_RULE_LINE_PATTERNS.get(canonical, ()))
    if code_snippet:
        for kw in _SNIPPET_KEYWORD_HINTS:
            if kw in code_snippet and kw not in patterns:
                patterns.append(kw)
    return patterns
def _read_source_lines(file_path: str) -> list[str] | None:
    file_path = _path_arg(file_path)
    if not file_path:
        return None
    source = read_source(file_path)
    if source is None:
        return None
    lines = source.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines
def _apply_line_strategies(lines: list[str], line: int,
                           patterns: list[str], code_snippet: str) -> int:
    if code_snippet:
        _hit = _locate_snippet_line(lines, code_snippet, line)
        if _hit >= 0:
            return _hit
    if line <= 0:
        return line
    _hit = _search_current_or_window(lines, line, patterns)
    if _hit >= 0:
        return _hit
    _hit = _locate_nearest_line(
        lines, line, lambda _ln: any(p in _ln for p in patterns))
    return _hit if _hit >= 0 else line
def revalidate_finding_line(file_path: str, line: int, rule_id: str,
                            code_snippet: str) -> int:
    line = coerce_line(line)
    rule_id = str_or(rule_id, "")
    file_path = _path_arg(file_path)
    if not isinstance(code_snippet, str):
        code_snippet = ""
    if not file_path or not os.path.isfile(file_path):
        return line
    lines = _read_source_lines(file_path)
    if lines is None:
        logger.warning(
            "[TreatmentStep] revalidate_finding_line read failed(%s), "
            "keeping line %d", file_path, line)
        return line
    patterns = _build_line_patterns(rule_id, code_snippet)
    if not patterns and not code_snippet.strip():
        return line
    return _apply_line_strategies(lines, line, patterns, code_snippet)
def _parse_fd_line(raw: object) -> int | None:
    line = coerce_line(raw)
    return line if line > 0 else None
def _file_stem(file_path: object) -> str:
    _name = _path_arg(file_path).replace("\\", "/").rsplit("/", 1)[-1]
    return os.path.splitext(_name)[0]
@dataclass(frozen=True)
class _SnippetAnchor:
    stem: str
    want_line: int
    path: str = ""
    rule_id: str = ""
def _snippet_rule_key(value) -> str:
    text = str_or(value, "").strip()
    return (canonical_rule_id(text) or text).casefold() if text else ""
def _source_path_parts(anchor_path: str, entry_path: str) -> tuple[list, list]:
    paths = tuple(_path_arg(path).replace("\\", "/")
                  for path in (anchor_path, entry_path))
    windows = os.name == "nt" or any(
        path.startswith("//") or (len(path) >= 2 and path[1] == ":")
        for path in paths)
    normalized = []
    for path in paths:
        parts = [part for part in path.split("/") if part]
        normalized.append([part.casefold() for part in parts] if windows else parts)
    return normalized[0], normalized[1]
def _source_path_is_absolute(path: str) -> bool:
    normalized = _path_arg(path).replace("\\", "/")
    return normalized.startswith("/") or (
        len(normalized) >= 3 and normalized[1] == ":"
        and normalized[2] == "/")
def _same_source_path(anchor_path: str, entry_path: str) -> bool:
    _parts_a, _parts_b = _source_path_parts(anchor_path, entry_path)
    if not _parts_a or not _parts_b:
        return False
    if _parts_a == _parts_b:
        return True
    if len(_parts_a) == 1 or len(_parts_b) == 1:
        _one_path = anchor_path if len(_parts_a) == 1 else entry_path
        return (not _source_path_is_absolute(_one_path)
                and _parts_a[-1] == _parts_b[-1])
    _short, _long = ((_parts_a, _parts_b) if len(_parts_a) <= len(_parts_b)
                     else (_parts_b, _parts_a))
    _short_path, _long_path = (
        (anchor_path, entry_path) if len(_parts_a) <= len(_parts_b)
        else (entry_path, anchor_path))
    if (_source_path_is_absolute(_short_path)
            or not _source_path_is_absolute(_long_path)):
        return False
    return _long[-len(_short):] == _short
def _entry_snippet_candidate(
    _fd: object, anchor: _SnippetAnchor,
) -> tuple[str | None, str]:
    if not isinstance(_fd, dict):
        return None, ""
    _raw_snippet = _fd.get("code_snippet", "")
    _snippet = _raw_snippet if isinstance(_raw_snippet, str) else ""
    if not _snippet:
        return None, ""
    if anchor.rule_id:
        candidate_rule = _snippet_rule_key(
            _fd.get("rule_id") or _fd.get("rule")
            or _fd.get("rule_family"))
        if candidate_rule != anchor.rule_id:
            return None, ""
    _entry_file = (_path_arg(_fd.get("file"))
                   or _path_arg(_fd.get("file_path")))
    if anchor.path:
        if not _same_source_path(anchor.path, _entry_file):
            return None, ""
    elif anchor.stem != _file_stem(_entry_file):
        return None, ""
    if anchor.want_line > 0 and _parse_fd_line(_fd.get("line")) == anchor.want_line:
        return _snippet, ""
    return None, _snippet if anchor.want_line <= 0 else ""
def _consolidated_findings_of(doc: dict) -> list:
    methods = doc.get("methods")
    if not isinstance(methods, dict):
        return []
    findings: list = []
    for payload in methods.values():
        if not isinstance(payload, dict):
            continue
        findings.extend(_dict_items(payload.get("findings_list")))
    return findings
def _load_diag_findings(json_path: str) -> list | None:
    try:
        with open(json_path, encoding="utf-8-sig") as _f:
            _data = json.load(_f)
    except Exception as e:
        logger.debug("JSON 解析失败（跳过）: %s", e, exc_info=True)
        return None
    if not isinstance(_data, dict):
        return None
    findings = _dict_items(_data.get("findings_list"))
    if findings:
        return findings
    _consolidated = _consolidated_findings_of(_data)
    if _consolidated:
        return _consolidated
    return None
def _find_snippet_matches_in_diag_json(
    json_path: str, anchor: _SnippetAnchor,
) -> tuple[list[tuple[str, str]], list[tuple[str, str]]]:
    findings = _load_diag_findings(json_path)
    if findings is None:
        return [], []
    matches: list[tuple[str, str]] = []
    fallbacks: list[tuple[str, str]] = []
    for finding in findings:
        hit, candidate_fallback = _entry_snippet_candidate(finding, anchor)
        if not hit and not candidate_fallback:
            continue
        entry_file = (_path_arg(finding.get("file"))
                      or _path_arg(finding.get("file_path")))
        if hit:
            matches.append((hit, entry_file))
        else:
            fallbacks.append((candidate_fallback, entry_file))
    return matches, fallbacks
def _select_snippet_match(matches: list[tuple[str, str]],
                          anchor: _SnippetAnchor) -> str:
    if not matches:
        return ""
    candidates = matches
    if anchor.path:
        exact_matches = []
        for match in matches:
            anchor_parts, candidate_parts = _source_path_parts(
                anchor.path, match[1])
            if anchor_parts == candidate_parts:
                exact_matches.append(match)
        if exact_matches:
            candidates = exact_matches
    if len({snippet for snippet, _ in candidates}) > 1:
        logger.warning(
            "[TreatmentStep] 诊断片段存在匹配歧义，拒绝任意选择: "
            "file=%s line=%d", anchor.path, anchor.want_line)
        return ""
    return candidates[0][0]
def _resolve_snippet_anchor(item: dict) -> _SnippetAnchor:
    item = item if isinstance(item, dict) else {}
    locator = str_or(item.get("locator"), "")
    target_file = (_path_arg(item.get("file_path"))
                   or _path_arg(item.get("file")))
    _anchor = target_file or _path_arg(parse_locator_file(locator))
    target_stem = _file_stem(_anchor)
    _want_line = parse_locator_line(locator) if locator else 0
    if _want_line <= 0:
        _want_line = coerce_line(item.get("line", 0))
    rule_id = _snippet_rule_key(
        item.get("rule_id") or item.get("rule") or item.get("rule_family"))
    return _SnippetAnchor(
        stem=target_stem, want_line=_want_line,
        path=_anchor, rule_id=rule_id)
def find_diag_snippet(sd: str, item: dict) -> str:
    sd = _path_arg(sd)
    if not sd.strip():
        logger.warning("[TreatmentStep] 技能根为空，跳过诊断片段定位")
        return ""
    try:
        diag_dir = json_artifact_dir(sd)
        if not os.path.isdir(diag_dir):
            return ""
        anchor = _resolve_snippet_anchor(item)
        if not anchor.stem:
            return ""
        for candidate in sorted(
                glob.glob(os.path.join(diag_dir, "*.json")), reverse=True):
            matches, fallbacks = _find_snippet_matches_in_diag_json(
                candidate, anchor)
            selected = _select_snippet_match(matches or fallbacks, anchor)
            if selected:
                return selected
            if matches or fallbacks:
                return ""
        return ""
    except Exception as e:
        logger.warning("[TreatmentStep] 诊断片段定位失败,片段降级为空: %s",
                       e, exc_info=True)
        return ""
_SEVERITY_CONTEXT_RADIUS: dict[str, int] = {"P0": 20, "P1": 16, "P2": 12}
_CONTEXT_RADIUS_DEFAULT = 8
_FUNCTION_FULL_COVER_LINES = 60
_CONTEXT_RADIUS_MAX = _FUNCTION_FULL_COVER_LINES - 1
def _full_function_cover(function_summary, line: int) -> int:
    if not isinstance(function_summary, dict):
        return 0
    line = coerce_line(line)
    lr = function_summary.get("line_range")
    if not (isinstance(lr, (list, tuple)) and len(lr) == 2
            and all(isinstance(x, int) and not isinstance(x, bool)
                    for x in lr)):
        return 0
    lo, hi = lr
    func_lines = hi - lo + 1
    if (0 < func_lines <= _FUNCTION_FULL_COVER_LINES
            and lo <= line <= hi):
        return max(line - lo, hi - line, 0)
    return 0
def _adaptive_context_radius(severity: str, function_summary: dict,
                            line: int) -> int:
    severity_key = severity.strip().upper() if isinstance(severity, str) else ""
    radius = _SEVERITY_CONTEXT_RADIUS.get(
        severity_key, _CONTEXT_RADIUS_DEFAULT)
    cover = _full_function_cover(function_summary, coerce_line(line))
    return min(max(radius, cover), _CONTEXT_RADIUS_MAX)
def _normalize_radius_arg(radius) -> int:
    if isinstance(radius, (int, float)) and not isinstance(radius, bool):
        try:
            if math.isfinite(radius):
                return max(0, int(radius))
        except OverflowError as _e:
            log_swallowed(
                __name__, _e, context='extract_code_context:OverflowError')
    logger.warning("[CodeContext] radius 形态非法（%r），回退默认 %d",
                   radius, _CONTEXT_RADIUS_DEFAULT)
    return _CONTEXT_RADIUS_DEFAULT
def _read_code_lines(filepath: str) -> list[str]:
    filepath = _path_arg(filepath)
    if not filepath or not os.path.isfile(filepath):
        return []
    lines = _read_source_lines(filepath)
    if lines is None:
        logger.warning("[CodeContext] 代码上下文读取失败，返回空: %s", filepath)
        return []
    return lines
def _render_window(lines: list[str], line_i: int, radius: int) -> str:
    _anchor = min(line_i, len(lines))
    start = max(0, _anchor - radius - 1)
    end = min(len(lines), _anchor + radius)
    return "\n".join(
        f"{'>>>' if (i + 1) == line_i else '   '} {i+1}: {lines[i].rstrip()}"
        for i in range(start, end))
def extract_code_context(filepath: str, line: int,
                         radius: int = _CONTEXT_RADIUS_DEFAULT, *,
                         severity: str = "",
                         function_summary: dict | None = None) -> str:
    lines = _read_code_lines(filepath)
    if not lines:
        return ""
    line_i = coerce_line(line)
    if not 0 < line_i <= len(lines):
        logger.debug(
            "[CodeContext] 无有效目标行，拒绝返回无关上下文: %s:%s",
            filepath, line)
        return ""
    radius = (_adaptive_context_radius(severity, function_summary, line_i)
              if severity or function_summary
              else _normalize_radius_arg(radius))
    return _render_window(lines, line_i, radius)
def extract_code_context_in_project(skill_dir: str, file_path, line) -> str:
    file_path = _path_arg(file_path)
    skill_dir = _path_arg(skill_dir)
    if not file_path or not skill_dir.strip():
        return ""
    _line = coerce_line(line)
    for _cand_path in dict.fromkeys((file_path, os.path.join(skill_dir, file_path))):
        candidate = canonical_path(_cand_path)
        if is_path_within_skill(candidate, skill_dir) and os.path.isfile(candidate):
            return extract_code_context(candidate, _line)
    return ""
_RAW_FINDING_DIGEST_KEYS: tuple[str, ...] = (
    "pattern", "matched_pattern", "signature", "ast_node_type",
    "node_type", "parent_function", "enclosing_scope", "detector",
    "engine", "phase", "line_end", "col_end", "end_lineno",
    "end_col_offset", "col_offset", "symbol", "name", "qualname",
    "category", "subcategory", "cwe", "owasp", "context_before",
    "context_after",
)
_RAW_FINDING_DIGEST_MAX_KEYS = 12
_DIGEST_LIST_STR_LIMIT = 100
_DIGEST_LIST_MAX_ITEMS = 5
_DIGEST_SCALAR_LIMIT = 200
_DIGEST_SKIP = object()
def _digest_scalar(value):
    if isinstance(value, bool) or is_real_number(value):
        return value
    if isinstance(value, str) and value:
        return value[:_DIGEST_SCALAR_LIMIT]
    return _DIGEST_SKIP
def _digest_list_items(value: list | tuple) -> list:
    items: list = []
    for v in value:
        if isinstance(v, bool):
            continue
        if isinstance(v, (int, float)):
            if is_real_number(v):
                items.append(v)
        elif isinstance(v, str):
            items.append(v[:_DIGEST_LIST_STR_LIMIT])
        if len(items) >= _DIGEST_LIST_MAX_ITEMS:
            break
    return items
def _digest_value(value):
    if isinstance(value, (list, tuple)):
        items = _digest_list_items(value)
        return items if items else _DIGEST_SKIP
    return _digest_scalar(value)
def _raw_finding_digest(raw_finding) -> dict:
    if not isinstance(raw_finding, dict):
        return {}
    digest: dict = {}
    for key in _RAW_FINDING_DIGEST_KEYS:
        coerced = _digest_value(raw_finding.get(key))
        if coerced is not _DIGEST_SKIP:
            digest[key] = coerced
        if len(digest) >= _RAW_FINDING_DIGEST_MAX_KEYS:
            break
    return digest
def build_diagnosis_evidence(item: dict, code_snippet: str) -> dict:
    item = item if isinstance(item, dict) else {}
    evidence = {
        "message": str_or(item.get("message"), ""),
        "code_snippet": str_or(code_snippet, ""),
        "sources": normalize_sources(item.get("sources")),
        "evidence_strength": float_field(item, "evidence_strength"),
        "adjusted_confidence": float_field(
            item, "adjusted_confidence"),
        "evidence_type": str_or(item.get("evidence_type"), ""),
        "conclusion": str_or(item.get("conclusion"), ""),
        "rule_applied": str_or(item.get("rule_applied"), ""),
        "locator": str_or(item.get("locator"), ""),
        "finding_id": str_or(item.get("finding_id"), ""),
        "notes": str_or(item.get("notes"), ""),
        "domain": str_or(item.get("domain"), ""),
    }
    _rf_digest = _raw_finding_digest(item.get("raw_finding"))
    if _rf_digest:
        evidence["raw_finding_digest"] = _rf_digest
    return evidence
_CACHE_MAX_ENTRIES = 256
_SUMMARY_CACHE: OrderedDict[str, Any] = OrderedDict()
_CACHE_LOCK = threading.Lock()
_CACHE_STATS = {"hits": 0, "misses": 0, "evictions": 0}
@dataclass
class SummaryCacheStats:
    total_entries: int = 0
    hits: int = 0
    misses: int = 0
    evictions: int = 0
    hit_rate: float = 0.0
    def to_dict(self) -> dict[str, Any]:
        return {
            "total_entries": self.total_entries,
            "hits": self.hits,
            "misses": self.misses,
            "evictions": self.evictions,
            "hit_rate": round(self.hit_rate, 4),
        }
def _cache_get(key: str) -> Any:
    with _CACHE_LOCK:
        if key not in _SUMMARY_CACHE:
            _CACHE_STATS["misses"] += 1
            return None
        _SUMMARY_CACHE.move_to_end(key)
        _CACHE_STATS["hits"] += 1
        return copy.deepcopy(_SUMMARY_CACHE[key])
def _cache_put(key: str, value: Any) -> None:
    with _CACHE_LOCK:
        if key in _SUMMARY_CACHE:
            _SUMMARY_CACHE.move_to_end(key)
            _SUMMARY_CACHE[key] = copy.deepcopy(value)
            return
        while len(_SUMMARY_CACHE) >= _CACHE_MAX_ENTRIES:
            _SUMMARY_CACHE.popitem(last=False)
            _CACHE_STATS["evictions"] += 1
        _SUMMARY_CACHE[key] = copy.deepcopy(value)
def get_summary_cache_stats() -> SummaryCacheStats:
    with _CACHE_LOCK:
        hits = _CACHE_STATS["hits"]
        misses = _CACHE_STATS["misses"]
        total = hits + misses
        return SummaryCacheStats(
            total_entries=len(_SUMMARY_CACHE),
            hits=hits,
            misses=misses,
            evictions=_CACHE_STATS["evictions"],
            hit_rate=(hits / total) if total > 0 else 0.0,
        )
def clear_summary_cache() -> int:
    with _CACHE_LOCK:
        n = len(_SUMMARY_CACHE)
        _SUMMARY_CACHE.clear()
        _CACHE_STATS.update({"hits": 0, "misses": 0, "evictions": 0})
        return n
_RETURN_NODE_LABELS = (
    (ast.Name, "variable"), (ast.Call, "call_result"),
    (ast.List, "list"), (ast.Dict, "dict"), (ast.Tuple, "tuple"),
)
_SIDE_EFFECT_ATTR_MAP = {
    "write": "file_write", "writelines": "file_write", "flush": "file_write",
    "append": "list_mutation", "extend": "list_mutation",
    "insert": "list_mutation", "remove": "list_mutation",
    "pop": "list_mutation", "sort": "list_mutation",
    "reverse": "list_mutation",
    "update": "dict_mutation", "popitem": "dict_mutation",
    "clear": "dict_mutation", "setdefault": "dict_mutation",
    "execute": "database", "commit": "database", "rollback": "database",
    "send": "network", "recv": "network", "connect": "network",
    "bind": "network", "listen": "network",
}
_SCOPE_MUTATION_LABELS = {
    ast.Global: "global_mutation",
    ast.Nonlocal: "nonlocal_mutation",
}
def _node_side_effect(node: ast.AST) -> str | None:
    label = _SCOPE_MUTATION_LABELS.get(type(node))
    if label is not None:
        return label
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
        return _SIDE_EFFECT_ATTR_MAP.get(node.func.attr)
    return None
_TAINT_SINK_NAMES = frozenset({
    "eval", "exec", "compile", "system", "popen", "execute", "run",
    "Popen", "check_output", "check_call", "getoutput",
})
def _return_value_label(value: ast.expr) -> str | None:
    if isinstance(value, ast.Constant):
        return "void" if value.value is None else type(value.value).__name__
    for tp, label in _RETURN_NODE_LABELS:
        if isinstance(value, tp):
            return label
    return None
def _iter_function_cards(tree: ast.AST):
    summarizer = FunctionSummarizer()
    for node in walk_nodes(tree):
        if isinstance(node, FUNC_NODE_TYPES) and not is_overload_stub(node):
            yield node, summarizer.summarize_node(node)
def _def_span(node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[int]:
    lo = min([node.lineno, *(dec.lineno for dec in node.decorator_list)])
    return [lo, node.end_lineno or node.lineno]
def _raise_target_name(exc: ast.expr) -> str | None:
    target = exc.func if isinstance(exc, ast.Call) else exc
    return expr_target_name(target) or None
def _iter_expr_scope_nodes(node: ast.AST):
    stack = [node]
    while stack:
        current = stack.pop()
        yield current
        if isinstance(current, _MODULE_SCOPE_BOUNDARY_NODES):
            continue
        stack.extend(ast.iter_child_nodes(current))
def _param_names_in_expr(node: ast.AST, params: set[str]) -> set[str]:
    found: set[str] = set()
    for child in _iter_expr_scope_nodes(node):
        if (isinstance(child, ast.Name)
                and isinstance(child.ctx, ast.Load)
                and child.id in params):
            found.add(child.id)
    return found
def _call_taint_flows(node: ast.Call,
                      params: set[str]) -> set[tuple[str, str]]:
    sink = expr_target_name(node.func)
    if sink not in _TAINT_SINK_NAMES:
        return set()
    return {(p, sink)
            for arg in [*node.args, *(kw.value for kw in node.keywords)]
            for p in _param_names_in_expr(arg, params)}
class FunctionSummarizer:
    def summarize_node(self, func_node: ast.FunctionDef | ast.AsyncFunctionDef) -> dict[str, Any]:
        return {
            "name": func_node.name,
            "params": self._extract_params(func_node),
            "returns": self._infer_return_type(func_node),
            "side_effects": self._detect_side_effects(func_node),
            "taint_propagation": self._infer_taint(func_node),
            "complexity": self._compute_complexity(func_node),
            "has_yield": self._has_yield(func_node),
            "has_async": isinstance(func_node, ast.AsyncFunctionDef),
            "raises": self._detect_raises(func_node),
        }
    def _extract_params(self, func_node: Any) -> list[str]:
        params = []
        for arg in (func_node.args.posonlyargs + func_node.args.args):
            params.append(arg.arg)
        if func_node.args.vararg:
            params.append(f"*{func_node.args.vararg.arg}")
        for arg in func_node.args.kwonlyargs:
            params.append(arg.arg)
        if func_node.args.kwarg:
            params.append(f"**{func_node.args.kwarg.arg}")
        return params
    def _infer_return_type(self, func_node: Any) -> str:
        labels = [
            (_return_value_label(node.value)
             if node.value is not None else "void")
            for node in iter_scope_nodes(func_node)
            if isinstance(node, ast.Return)
        ]
        if not labels:
            return "void"
        distinct = set(labels)
        if len(distinct) > 1:
            return "mixed"
        label = distinct.pop()
        return "unknown" if label is None else label
    def _detect_side_effects(self, func_node: Any) -> list[str]:
        effects = {_node_side_effect(node)
                   for node in iter_scope_nodes(func_node)}
        effects.discard(None)
        return sorted(effects)
    def _infer_taint(self, func_node: Any) -> dict[str, Any]:
        params = {p.lstrip("*") for p in self._extract_params(func_node)}
        taint_to: set[tuple[str, str]] = set()
        for node in iter_scope_nodes(func_node):
            if isinstance(node, ast.Call):
                taint_to |= _call_taint_flows(node, params)
        if not taint_to:
            return {}
        return {"taint_flows": [
            {"param": p, "sink": s} for p, s in sorted(taint_to)]}
    def _compute_complexity(self, func_node: Any) -> int:
        return 1 + decision_points(func_node, iter_scope_nodes)
    def _has_yield(self, func_node: Any) -> bool:
        for node in iter_scope_nodes(func_node):
            if isinstance(node, (ast.Yield, ast.YieldFrom)):
                return True
        return False
    def _detect_raises(self, func_node: Any) -> list[str]:
        names = {_raise_target_name(node.exc)
                 for node in iter_scope_nodes(func_node)
                 if isinstance(node, ast.Raise) and node.exc is not None}
        names.discard(None)
        return sorted(names)
def _resolve_source(filepath: str, source: str | None) -> tuple[str | None, dict | None]:
    if source is not None:
        if isinstance(source, str):
            return source, None
        logger.warning("summarize_file: source 非 str（%s），返回错误卡片",
                       type(source).__name__)
        return None, {"_error": {"invalid_source": f"expected str, got {type(source).__name__}"}}
    resolved_path = _path_arg(filepath)
    if not resolved_path:
        logger.warning("无法读取文件 %s: filepath 非 str/PathLike（%s）",
                       filepath, type(filepath).__name__)
        return None, {"_error": {
            "invalid_path": (
                f"expected str or PathLike, got {type(filepath).__name__}")}}
    resolved = read_cached(resolved_path)
    if resolved is None:
        logger.warning("无法读取文件 %s: 读取或解码失败（解释器同口径）",
                       filepath)
        return None, {}
    return resolved, None
def _function_qualnames(tree: ast.AST) -> dict[int, str]:
    parents: dict[int, ast.AST] = {}
    for parent in walk_nodes(tree):
        for child in ast.iter_child_nodes(parent):
            parents[id(child)] = parent
    qualified: dict[int, str] = {}
    scope_nodes = (*FUNC_NODE_TYPES, ast.ClassDef)
    for node in walk_nodes(tree):
        if not isinstance(node, FUNC_NODE_TYPES):
            continue
        parts = [node.name]
        current = parents.get(id(node))
        while current is not None:
            if isinstance(current, scope_nodes):
                parts.append(current.name)
            current = parents.get(id(current))
        qualified[id(node)] = ".".join(reversed(parts))
    return qualified
def _unique_summary_key(base: str, node, summaries: dict) -> str:
    key = base
    if key in summaries:
        key = f"{base}@L{node.lineno}"
    suffix = 2
    while key in summaries:
        key = f"{base}@L{node.lineno}-{suffix}"
        suffix += 1
    return key
def _summarize_file_cards(tree: ast.AST) -> dict[str, dict[str, Any]]:
    grouped: dict[str, list[tuple[Any, dict[str, Any]]]] = {}
    for node, card in _iter_function_cards(tree):
        grouped.setdefault(node.name, []).append((node, card))
    qualnames = _function_qualnames(tree)
    summaries: dict[str, dict[str, Any]] = {}
    for name, cards in grouped.items():
        if len(cards) == 1:
            summaries[name] = cards[0][1]
            continue
        bases = [qualnames[id(node)] or node.name for node, _ in cards]
        colliding = {base for base in bases if bases.count(base) > 1}
        for node, card in cards:
            base = qualnames[id(node)] or node.name
            if base == name or base in colliding:
                base = f"{base}@L{node.lineno}"
            key = _unique_summary_key(base, node, summaries)
            summaries[key] = card
    return summaries
def summarize_file(filepath: str, source: str | None = None) -> dict[str, dict[str, Any]]:
    source, failure = _resolve_source(filepath, source)
    if failure is not None:
        return failure
    cache_key = f"file::{source_digest(source)}"
    cached = _cache_get(cache_key)
    if cached is not None:
        return cached
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.warning("文件 %s 语法错误或解析降级: %s", filepath, e)
        return {"_error": {"syntax_error": str(e)}}
    summaries = _summarize_file_cards(tree)
    _cache_put(cache_key, summaries)
    return summaries
def _atline_file_cards(source: str, filepath: str) -> dict[str, dict[str, Any]] | None:
    try:
        tree = parse_cached(source)
    except PARSE_DEGRADE_EXC as e:
        logger.debug("summarize_function_at_line(%s) 解析失败: %s", filepath, e)
        return None
    per_file: dict[str, dict[str, Any]] = {}
    for node, card in _iter_function_cards(tree):
        card["line_range"] = _def_span(node)
        per_file[f"L{node.lineno}:{node.name}"] = card
    return per_file
def _normalize_atline_line(filepath: str, line: int) -> int | None:
    if not _path_arg(filepath) or isinstance(line, bool):
        return None
    normalized = coerce_line(line)
    return normalized if normalized > 0 else None
def _locate_innermost_card(per_file: dict[str, dict[str, Any]], line: int) -> dict[str, Any]:
    spans = [((card["line_range"][1] - card["line_range"][0]), card)
             for card in per_file.values()
             if card["line_range"][0] <= line <= card["line_range"][1]]
    return min(spans, key=lambda item: item[0])[1] if spans else {}
def summarize_function_at_line(filepath: str, line: int) -> dict[str, Any]:
    filepath = _path_arg(filepath)
    normalized = _normalize_atline_line(filepath, line)
    if normalized is None:
        logger.debug("summarize_function_at_line(%s:%s) 参数归一失败: 非法 filepath/line",
                     filepath, line)
        return {}
    source = read_cached(filepath)
    if source is None:
        logger.debug("summarize_function_at_line(%s:%s) 读取失败: 不可读或不可解码",
                     filepath, line)
        return {}
    cache_key = f"atline::{source_digest(source)}"
    per_file = _cache_get(cache_key)
    if per_file is None:
        per_file = _atline_file_cards(source, filepath)
        if per_file is None:
            return {}
        _cache_put(cache_key, per_file)
    return _locate_innermost_card(per_file, normalized)
def _load_cv_entries(skill_dir: str) -> tuple[list, str]:
    skill_dir = _path_arg(skill_dir)
    if not skill_dir.strip():
        logger.warning("[AnalysisContext] 技能根为空，跳过 CV 结论索引")
        return [], ""
    try:
        temp_base = get_temp_dir(skill_dir)
        meta = load_cv_findings_index(temp_base, return_meta=True)
    except Exception:
        logger.warning("[AnalysisContext] CV 结论索引加载失败，降级为无 CV 信息", exc_info=True)
        return [], ""
    entries = (_dict_items(meta.get("findings_index"))
               if isinstance(meta, dict) else [])
    if not entries:
        return [], ""
    return entries, str_or(meta.get("source_ts"), "")
def _cv_family_key(value) -> str:
    return str_or(value, "").strip().casefold()
def _cv_evidence_rank(context: dict) -> tuple[int, float]:
    return (
        max(0, plan_index(context.get("cv_source_count", 0)) or 0),
        float_field(context, "cv_confidence"),
    )
def _cv_entry(entry, source_ts: str,
              skill_dir: str) -> tuple[tuple, dict, str] | None:
    if not isinstance(entry, dict):
        return None
    e = entry
    fpath = canonical_cv_path(
        _path_arg(e.get("file")) or _path_arg(e.get("file_path")),
        skill_dir or None)
    line_i = coerce_line(e.get("line", 0))
    confidence = safe_float(e.get(FIELD_ADJUSTED_CONFIDENCE), None)
    if confidence is None:
        confidence = float_field(e, "confidence")
    ctx = {
        "cv_conclusion": str_or(e.get("conclusion"), ""),
        "cv_confidence": confidence,
        "cv_source_count": max(0, plan_index(e.get("source_count", 0)) or 0),
        "cv_locator": str_or(e.get("locator"), ""),
        "cv_matched_rule": str_or(e.get("rule_id"), ""),
        "cv_rule_family": str_or(e.get("rule_family"), ""),
        "cv_source_ts": source_ts,
    }
    fam = str_or(e.get("rule_family"), "")
    return (fpath, line_i), ctx, fam
class CvContextIndex:
    def __init__(self, exact: dict, by_line: dict,
                 skill_dir: str = "") -> None:
        self.exact = exact
        self.by_line = by_line
        self.skill_dir = skill_dir
    @classmethod
    def load(cls, skill_dir: str) -> CvContextIndex:
        skill_dir = _path_arg(skill_dir)
        entries, source_ts = _load_cv_entries(skill_dir)
        exact: dict[tuple, dict] = {}
        by_line: dict[tuple, list] = {}
        for e in entries:
            _entry = _cv_entry(e, source_ts, skill_dir)
            if _entry is None:
                continue
            _key, _ctx, _fam = _entry
            family_key = _cv_family_key(_fam)
            if family_key:
                exact_key = (*_key, family_key)
                current = exact.get(exact_key)
                if (current is None
                        or _cv_evidence_rank(_ctx)
                        > _cv_evidence_rank(current)):
                    exact[exact_key] = _ctx
            by_line.setdefault(_key, []).append(_ctx)
        return cls(exact, by_line, skill_dir)
    def match(self, file_path: str, line, rule_family: str) -> dict | None:
        file_key = _path_arg(file_path)
        if not file_key:
            return None
        line_i = coerce_line(line)
        key = (canonical_cv_path(file_key, self.skill_dir or None), line_i)
        family_key = _cv_family_key(rule_family)
        hit = (self.exact.get((key[0], line_i, family_key))
               if family_key else None)
        if hit:
            return dict(hit)
        candidates = self.by_line.get(key) or []
        if not candidates:
            return None
        present_families = {
            _cv_family_key(c.get("cv_rule_family")) for c in candidates
            if _cv_family_key(c.get("cv_rule_family"))
        }
        if family_key:
            if present_families - {family_key}:
                return None
            candidates = [
                c for c in candidates
                if _cv_family_key(c.get("cv_rule_family")) == family_key
            ]
        elif len(present_families) > 1:
            return None
        if not candidates:
            return None
        return dict(max(candidates, key=_cv_evidence_rank))
    def __bool__(self) -> bool:
        return bool(self.exact) or bool(self.by_line)
register_cache_release(
    "summary_cache", clear_summary_cache, "修复摘要缓存", order=180)

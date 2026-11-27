from __future__ import annotations

import ast
import copy
import hashlib
import importlib
import inspect
import json
import logging
import os
import re
import threading
import time
from collections.abc import Callable, Iterator, Mapping
from dataclasses import dataclass, field, replace
from functools import lru_cache
from pathlib import Path
from types import SimpleNamespace
from typing import Any, ClassVar, NamedTuple

from jwsgj.diag_detector_findings import (
    apply_suppress_filter,
    category_from_rule_id,
    deduplicate_issues,
    extend_issues,
    finding_rule_id,
    is_retired_rule,
    normalize_id_set,
    normalize_severity,
    to_issue_dict,
)
from jwsgj.diag_detectors_registry import (
    EXEC_SWALLOWED_EXCEPTIONS,
    GATE_RULE_MODULES,
    WIRING_MODULES,
    detector_catalog,
    early_channel,
    early_channels,
    engine_channels,
    get_registry,
    init_reentrant,
    register_detector_catalog,
    register_rebuild_hook,
    set_auto_register_hook,
    set_registry_reset_hook,
)
from jwsgj.diag_guard_io import atomic_write_text
from jwsgj.diag_shared_source_core import (
    aligned_source_lines,
    is_memory_source,
    read_py_source,
    read_shared_snapshot,
    read_source_with_fingerprint,
    register_memory_source,
    unregister_memory_source,
)
from jwsgj.diag_shared_source_scan import comment_tokens
from jwsgj.diag_types_defs import (
    DiagnoseIssue,
    PatternFinding,
    PreinterventionResult,
    ProjectContext,
    aaf_reject,
    collect_findings,
    issue_to_finding,
    make_detail,
)
from jwsgj.diag_types_normalize import (
    coerce_line,
    coerce_line_number,
    coerce_tolerance,
    normalize_input,
    rule_id_of,
    safe_confidence,
    severity_text_value,
    signal_bool,
    strip_bom,
)
from jwsgj.diag_types_vocab import (
    MSG_SYNTAX_ERROR_SKIP,
    PARSE_DEGRADE_EXC,
    SEVERITY_BLOCKING,
    SEVERITY_INFO,
    SEVERITY_PENALTY_WEIGHTS,
    SEVERITY_RANK,
    SEVERITY_WARNING,
    VULN_RENDER_TEMPLATE,
    WIRING_DECLARATION_ATTR,
    DiagnoseSeverity,
    diag_severity_to_p,
    register_check_provider,
    register_review_provider,
)
from jwsgj.log_config import (
    log_swallowed,
    write_audit,
    write_module_run,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import get_temp_base
from jwsgj.runtime_scope import (
    is_appledouble_basename,
    is_audit_skip_dir,
    is_pruned_scan_dir,
    is_test_file_path,
    scan_prune_dirs,
)

__all__ = [
    "AICODER_DIRECT_CHECKS",  # noqa: F822
    "AUDIT_DETECTOR_IDS",
    "DIAG4_DIRECT_CHECKS",  # noqa: F822
    "RD_PREVENTION_CHECKS",  # noqa: F822
    "SCORE_WEIGHTS",
    "ContextAwareFilter",
    "ContextExtractor",
    "ContextRuleSet",
    "DiagnoseBlockedError",
    "DiagnoseGate",
    "DiagnoseGateResult",
    "DiagnosisBaseline",
    "DiagnosisRegressionGuard",
    "GateScanCache",
    "aaf_verify_diag",
    "audit_detector_classes",
    "audit_registry_class_ids",
    "bounded_cache_put",
    "build_diag_baseline",
    "build_diagnose_gate_detectors",
    "check_bug_antipatterns",
    "check_diag_regression",
    "check_over_engineering",
    "clear_project_context_cache",
    "detect_all",
    "detect_all_audit_patterns",
    "detect_all_new_patterns",
    "ensure_wirings_registered",
    "filter_findings_with_context",
    "gate_issue_severity",
    "get_gate",
    "load_source_and_tree",
    "make_gate_adapter",
    "quick_audit_pattern_check",
    "quick_context_extract",
    "quick_context_filter",
    "quick_new_pattern_check",
    "registry_sec_family_ids",
    "to_gate_finding",
]
_log = logging.getLogger(__name__)
_GATE_CACHE_META_KEY = '_rules_key'
_GATE_CACHE_EXEMPT_KEY = '_d01_exempt_key'
_GATE_CACHE_META_KEYS = frozenset({_GATE_CACHE_META_KEY, _GATE_CACHE_EXEMPT_KEY})
def _gate_cache_name(skill_dir) -> str:
    project_id = os.path.normcase(os.path.realpath(os.path.abspath(skill_dir)))
    digest = hashlib.sha256(os.fsencode(project_id)).hexdigest()
    return f'{digest}.json'
def _gate_scan_cache_path(skill_dir) -> Path:
    return (Path(get_temp_base(str(skill_dir))) / 'sec_gate_scan_cache'
            / _gate_cache_name(skill_dir))
def _gate_scan_shared_cache_path(skill_dir) -> Path:
    return (Path(get_temp_base(str(skill_dir))) / '_sec_gate_scan_cache'
            / _gate_cache_name(skill_dir))
_GATE_CACHE_LAYERS = ((_gate_scan_cache_path, '会话层'),
                      (_gate_scan_shared_cache_path, '共享层'))
def _gate_cache_layers(skill_dir) -> tuple:
    return tuple((build_path(skill_dir), layer)
                 for build_path, layer in _GATE_CACHE_LAYERS)
def _d01_exempt_fingerprint(exempt) -> str:
    try:
        _norm = sorted((str(m), str(t)) for m, t in (exempt or ()))
        return hashlib.sha256(repr(_norm).encode('utf-8')).hexdigest()
    except Exception:  # noqa: BLE001
        _log.debug('D01 豁免集指纹计算失败，降级 unversioned（触发全量重扫）',
                   exc_info=True)
        return 'unversioned'
def _read_cache_json(path) -> dict | None:
    try:
        data = json.loads(strip_bom(Path(path).read_text(encoding='utf-8')))
    except Exception:  # noqa: BLE001
        _log.debug('门禁扫描缓存解析失败，按未命中处理: %s', path, exc_info=True)
        return None
    return data if isinstance(data, dict) else None
def _load_valid_cache_entry(path, rules_key: str, exempt_key: str,
                            layer: str) -> dict:
    try:
        if not Path(path).exists():
            return {}
        if 'unversioned' in (rules_key, exempt_key):
            _log.info('门禁扫描缓存%s指纹不可用（规则/豁免集），强制全量重扫', layer)
            return {}
        data = _read_cache_json(path)
        if data is None:
            return {}
        if (data.get(_GATE_CACHE_META_KEY) == rules_key
                and data.get(_GATE_CACHE_EXEMPT_KEY) == exempt_key):
            return data
        _log.info('门禁扫描缓存指纹变更（规则/豁免集，%s），全量重扫', layer)
        return {}
    except Exception:  # noqa: BLE001
        _log.debug('门禁扫描缓存%s加载失败，按未命中处理', layer, exc_info=True)
        return {}
_MISSING_FIELD = object()
def _finding_field(finding: Any, name: str, default: Any = None) -> Any:
    if isinstance(finding, Mapping):
        value = finding.get(name, _MISSING_FIELD)
    else:
        value = getattr(finding, name, _MISSING_FIELD)
    return default if value is _MISSING_FIELD else value
def _finding_rule_identity(finding: Any) -> Any:
    return (_finding_field(finding, 'check_id', '')
            or _finding_field(finding, 'rule_id', ''))
def _norm_gate_severity(value) -> DiagnoseSeverity:
    if isinstance(value, DiagnoseSeverity):
        return value
    severity = _gate_enum_from_text(value)
    return severity if severity is not None else DiagnoseSeverity.ERROR
def _cached_gate_issue(item: dict) -> SimpleNamespace:
    return SimpleNamespace(
        check_id=item.get('check_id') or '',
        severity=_norm_gate_severity(item.get('severity')),
        message=item.get('message') or '',
        line=coerce_line_number(item.get('line')),
        suggestion=item.get('suggestion') or '')
def _cache_issues_usable(issues) -> bool:
    return (isinstance(issues, list)
            and all(isinstance(_i, dict) for _i in issues))
def _gate_issue_row(issue) -> dict:
    return {'check_id': _finding_rule_identity(issue),
            'severity': _norm_gate_severity(
                _finding_field(issue, 'severity')).name,
            'message': _finding_field(issue, 'message', ''),
            'line': coerce_line(_finding_field(issue, 'line', 0)),
            'suggestion': _finding_field(issue, 'suggestion', '')}
def _is_stale_entry(key: str, seen: set[str]) -> bool:
    return key not in seen and key not in _GATE_CACHE_META_KEYS
@dataclass
class GateScanCache:
    skill_dir: str
    exempt: set | frozenset | tuple = field(default_factory=set)
    rules_key_provider: Callable[[], str] | None = None
    def _rules_key(self) -> str:
        if self.rules_key_provider is None:
            return 'unversioned'
        try:
            value = self.rules_key_provider()
            if value is None:
                return 'unversioned'
            return str(value).strip() or 'unversioned'
        except Exception:  # noqa: BLE001
            _log.debug('门禁扫描缓存规则指纹提供方失败，强制全量重扫', exc_info=True)
            return 'unversioned'
    def load(self) -> dict:
        try:
            layers = _gate_cache_layers(self.skill_dir)
            if not any(path.exists() for path, _layer in layers):
                return {}
        except Exception:  # noqa: BLE001
            _log.debug('门禁扫描缓存层不可用，按无缓存全量扫描', exc_info=True)
            return {}
        rules_key = self._rules_key()
        exempt_key = _d01_exempt_fingerprint(self.exempt)
        for path, layer in layers:
            data = _load_valid_cache_entry(path, rules_key, exempt_key, layer)
            if data:
                return data
        return {}
    def save(self, entries: dict) -> None:
        _payload: str | None = None
        try:
            layers = _gate_cache_layers(self.skill_dir)
        except Exception as _layers_exc:  # noqa: BLE001
            _log.warning('门禁扫描缓存层解析失败，跳过写盘: %s', _layers_exc,
                         exc_info=True)
            return
        for path, layer in layers:
            try:
                path.parent.mkdir(parents=True, exist_ok=True)
                if _payload is None:
                    payload_entries = dict(entries)
                    payload_entries[_GATE_CACHE_META_KEY] = self._rules_key()
                    payload_entries[_GATE_CACHE_EXEMPT_KEY] = (
                        _d01_exempt_fingerprint(self.exempt))
                    _payload = json.dumps(payload_entries, ensure_ascii=False,
                                          default=str)
                atomic_write_text(str(path), _payload, tag='sec_gate_cache')
            except Exception as _cache_exc:  # noqa: BLE001
                _log.warning('门禁扫描缓存%s写盘失败，下次全量重扫: %s',
                             layer, _cache_exc, exc_info=True)
    @staticmethod
    def issues_for(entries: dict, rel: str, content_hash: str):
        cached = entries.get(rel)
        if not isinstance(cached, dict) or cached.get('hash') != content_hash:
            return None
        issues = cached.get('issues')
        if not _cache_issues_usable(issues):
            return None
        return [_cached_gate_issue(i) for i in issues]
    @staticmethod
    def store(entries: dict, rel: str, content_hash: str, issues: list) -> None:
        if any(_finding_rule_identity(i) == 'D29' for i in issues):
            entries.pop(rel, None)
            return
        entries[rel] = {'hash': content_hash,
                        'issues': [_gate_issue_row(i) for i in issues]}
    @staticmethod
    def prune(entries: dict, seen: set[str]) -> bool:
        if not entries:
            return False
        _stale = [k for k in entries if _is_stale_entry(k, seen)]
        for key in _stale:
            entries.pop(key, None)
        return bool(_stale)
@dataclass
class DiagnoseGateResult:
    ok: bool
    issues: list[DiagnoseIssue] = field(default_factory=list)
    block_count: int = 0
    error_count: int = 0
    warn_count: int = 0
    message: str = ''
def _blocked_result(issue: DiagnoseIssue,
                    message: str = '语法错误,阻断写入') -> DiagnoseGateResult:
    return DiagnoseGateResult(ok=False, issues=[issue], block_count=1,
                              message=message)
def _d29_block_issue(message: str, suggestion: str, line: int = 0) -> DiagnoseIssue:
    return DiagnoseIssue(
        check_id='D29', severity=DiagnoseSeverity.BLOCK,
        message=message, line=line, suggestion=suggestion)
def _non_str_code_issue(code: object) -> DiagnoseIssue:
    return _d29_block_issue(
        f'输入契约违约: code 参数非 str（{type(code).__name__}），无法解析检测',
        '传入 str 源码（bytes 请先 decode）后再检测')
def _non_module_tree_issue(tree: object) -> DiagnoseIssue:
    return _d29_block_issue(
        f'输入契约违约: 传入树非 Module（{type(tree).__name__}）',
        '检查调用方 AST 传递')
def _parse_source_tree(code: str) -> tuple[ast.AST | None, DiagnoseGateResult | None]:
    try:
        return ast.parse(code), None
    except PARSE_DEGRADE_EXC as e:
        log_swallowed(
            __name__, e,
            context=f'DiagnoseGate._parse_source_tree:{type(e).__name__}')
        return None, _blocked_result(_d29_block_issue(
            f'语法错误: {getattr(e, "msg", str(e))}',
            '修复语法错误后重试', getattr(e, 'lineno', 0) or 0))
def _resolve_scan_tree(
    code: object, tree: ast.AST | None,
) -> tuple[str | None, ast.AST | None, DiagnoseGateResult | None]:
    if tree is not None and not isinstance(tree, ast.Module):
        return None, None, _blocked_result(
            _non_module_tree_issue(tree), '输入契约违约,阻断写入')
    if code is None or (isinstance(code, str) and not code.strip()):
        if tree is None:
            return None, None, None
        code = ast.unparse(tree)
        return (code, tree, None) if code.strip() else (code, None, None)
    if not isinstance(code, str):
        return None, None, _blocked_result(
            _non_str_code_issue(code), '输入契约违约,阻断写入')
    if tree is None:
        parsed, early_result = _parse_source_tree(code)
        return code, parsed, early_result
    return code, tree, None
_GATE_SEVERITY_ENUM = {severity.value: severity for severity in DiagnoseSeverity}
_GATE_SEVERITY_BY_RANK: dict[int, DiagnoseSeverity] = {
    0: DiagnoseSeverity.BLOCK,
    1: DiagnoseSeverity.ERROR,
    2: DiagnoseSeverity.WARN,
    3: DiagnoseSeverity.INFO,
    4: DiagnoseSeverity.INFO,
}
def _gate_enum_from_text(value) -> DiagnoseSeverity | None:
    text = severity_text_value(value)
    if text is None:
        return None
    gate_severity = _GATE_SEVERITY_ENUM.get(text)
    if gate_severity is not None:
        return gate_severity
    rank = SEVERITY_RANK.get(text)
    return _GATE_SEVERITY_BY_RANK.get(rank) if rank is not None else None
_DEFAULT_FINDING_SEVERITY = 'MEDIUM'
def _finding_severity(finding) -> str:
    return (severity_text_value(_finding_field(finding, 'severity'))
            or _DEFAULT_FINDING_SEVERITY)
def gate_issue_severity(finding) -> str:
    severity = _gate_enum_from_text(_finding_field(finding, 'severity'))
    return severity.value if severity is not None else DiagnoseSeverity.ERROR.value
def _iter_detector_findings(result: Any) -> Iterator[Any] | None:
    if result is None:
        return iter(())
    if isinstance(result, Mapping):
        return iter((result,))
    if isinstance(result, (str, bytes)):
        return None
    try:
        return iter(result)
    except TypeError:
        return None
def _degraded_channel_issue(label: str, exc: Exception, filepath: Any,
                            skill_dir: Any = "",
                            failure: str = "结果迭代失败") -> dict:
    return to_issue_dict({
        "rule_id": "GATE-DEGRADED",
        "message": (f"检测通道 {label} {failure}"
                    f"（{type(exc).__name__}），该通道检查未完成"),
        "severity": "ERROR",
        "line": 0,
        "suggestion": "修复检测通道的惰性结果生成逻辑后重试",
    }, filepath, skill_dir=skill_dir)
def _run_channel_checked(label: str, run: Callable[[], Any], filepath: Any,
                         skill_dir: Any) -> Any:
    try:
        return run()
    except EXEC_SWALLOWED_EXCEPTIONS as exc:
        _log.warning("[Detectors] %s 执行失败，已标记降级: %s",
                     label, exc, exc_info=True)
        return [_degraded_channel_issue(label, exc, filepath, skill_dir)]
def _extend_detector_channel_issues(all_issues: list, raw: Any, label: str,
                                    filepath: Any, skill_dir: Any) -> None:
    items = _iter_detector_findings(raw)
    if items is None:
        _log.warning(
            "[Detectors] %s 通道返回契约外结果（%s），标记降级",
            label, type(raw).__name__)
        all_issues.append(_degraded_channel_issue(
            label, TypeError("检测器必须返回可迭代的发现序列"),
            filepath, skill_dir))
        return
    produced = 0
    try:
        for item in items:
            if item is not None:
                all_issues.append(to_issue_dict(
                    item, filepath, skill_dir=skill_dir))
                produced += 1
    except Exception as exc:  # noqa: BLE001
        _log.warning(
            "[Detectors] %s 通道结果迭代失败，保留已产出的 %d 条并标记降级: %s",
            label, produced, exc, exc_info=True)
        all_issues.append(_degraded_channel_issue(
            label, exc, filepath, skill_dir))
def _coerce_issue_details(value) -> dict:
    if isinstance(value, Mapping):
        return dict(value)
    if value is not None:
        _log.debug('检测器发现 details 非映射(%s)，按空映射处理',
                   type(value).__name__)
    return {}
def _normalize_detector_issue(issue) -> DiagnoseIssue:
    severity = (_gate_enum_from_text(_finding_field(issue, 'severity'))
                or DiagnoseSeverity.ERROR)
    if isinstance(issue, DiagnoseIssue):
        return replace(
            issue,
            check_id=str(issue.check_id or ''),
            severity=severity,
            message=str(issue.message or ''),
            line=coerce_line_number(issue.line),
            suggestion=str(issue.suggestion or ''),
            auto_fixable=signal_bool(issue.auto_fixable),
            details=_coerce_issue_details(issue.details),
        )
    return DiagnoseIssue(
        check_id=str(_finding_rule_identity(issue) or ''),
        severity=severity,
        message=str(_finding_field(issue, 'message', '') or ''),
        line=coerce_line_number(_finding_field(issue, 'line')),
        suggestion=str(_finding_field(issue, 'suggestion', '') or ''),
        auto_fixable=signal_bool(
            _finding_field(issue, 'auto_fixable', False)),
        details=_coerce_issue_details(_finding_field(issue, 'details')))
def _carrier_value(raw) -> Any:
    if isinstance(raw, Mapping):
        return raw.get('value', raw)
    return getattr(raw, 'value', raw)
def _finding_category(finding) -> str:
    category = _finding_field(finding, 'category')
    return str(_carrier_value(category)) if category else 'unknown'
def _finding_suggestion(finding) -> str:
    suggestion = _finding_field(finding, 'suggestion', '')
    if not suggestion:
        return ""
    return suggestion if isinstance(suggestion, str) else str(suggestion)
def _finding_line(finding) -> int:
    return coerce_line_number(_finding_field(finding, 'line'))
def _finding_confidence(finding) -> float:
    return safe_confidence(_finding_field(finding, 'confidence', 1.0), 1.0)
def _finding_check_id(cwe_id: object, category_name: object) -> str:
    return f'SEC-{cwe_id}' if cwe_id else f'SEC-{category_name}'
_FALSE_POSITIVE_TRUE_STRINGS = frozenset({'1', 'true'})
def _finding_is_false_positive(finding) -> bool:
    raw = _finding_field(finding, 'is_false_positive', False)
    if isinstance(raw, bool):
        return raw
    if isinstance(raw, str):
        return raw.strip().lower() in _FALSE_POSITIVE_TRUE_STRINGS
    if isinstance(raw, (int, float)):
        return raw == 1
    return False
def _finding_message(category_name: object, sev_str: object,
                     source: object, sink: object, cwe_id: object) -> str:
    message = f'安全发现: {category_name} ({sev_str}) source={source} sink={sink}'
    if cwe_id:
        message += f' [{cwe_id}]'
    return message
_SECURITY_FINDINGS_TYPES = (list, tuple, set, frozenset)
_SecurityFindings = list | tuple | set | frozenset
_SECURITY_FINDING_FIELDS: tuple[str, ...] = (
    'severity', 'category', 'cwe_id', 'confidence', 'source', 'sink',
    'suggestion', 'line', 'file', 'is_false_positive',
)
def _security_findings_container_error(findings: object) -> DiagnoseIssue | None:
    if isinstance(findings, _SECURITY_FINDINGS_TYPES):
        return None
    return DiagnoseIssue(
        check_id='SEC-INPUT', severity=DiagnoseSeverity.BLOCK,
        message=(f'安全发现载荷非 list/tuple/set/frozenset'
                 f'（{type(findings).__name__}），无法消费'),
        line=0,
        suggestion='传入 VulnerabilityFinding 列表（或鸭子类型对象列表）')
def _security_finding_payload_error(finding: object,
                                    index: int) -> DiagnoseIssue | None:
    if isinstance(finding, Mapping):
        if any(name in finding for name in _SECURITY_FINDING_FIELDS):
            return None
    elif any(hasattr(finding, name) for name in _SECURITY_FINDING_FIELDS):
        return None
    return DiagnoseIssue(
        check_id='SEC-INPUT', severity=DiagnoseSeverity.BLOCK,
        message=(f'安全发现第 {index} 条载荷无可用字段'
                 f'（{type(finding).__name__}），无法消费'),
        line=0,
        suggestion='传入带 severity/category 等字段的发现对象或映射')
def _severity_counts(issues: list) -> dict[DiagnoseSeverity, int]:
    counts = dict.fromkeys((DiagnoseSeverity.BLOCK, DiagnoseSeverity.ERROR,
                            DiagnoseSeverity.WARN), 0)
    for issue in issues:
        if issue.severity in counts:
            counts[issue.severity] += 1
    return counts
_AUDIT_SAMPLE_LIMIT = 20
def _audit_blocked_security(issues: list, filepath: str) -> None:
    blocked = [i for i in issues if i.severity == DiagnoseSeverity.BLOCK]
    if not blocked:
        return
    sample = blocked[:_AUDIT_SAMPLE_LIMIT]
    try:
        write_audit(
            'security_finding_blocked',
            block_count=len(blocked),
            error_count=_severity_counts(issues)[DiagnoseSeverity.ERROR],
            sampled_count=len(sample),
            truncated=len(blocked) > len(sample),
            findings=[{'check_id': i.check_id,
                       'message': i.message[:200],
                       'file': i.details.get('file', filepath)}
                      for i in sample])
    except Exception:  # noqa: BLE001
        _log.warning('安全发现审计写入失败, 跳过', exc_info=True)
DEFAULT_GATE_STRICT: bool = True
class DiagnoseGate:
    def __init__(self, strict: bool = DEFAULT_GATE_STRICT):
        self.strict = signal_bool(strict)
        self._detectors: dict[str, Callable] = {}
        self.d01_cycle_exempt: set[tuple[str, str]] = set()
        self._register_builtin_detectors()
    _QUICK_RULE_IDS: ClassVar[tuple[str, ...]] = ('D06', 'D13', 'D29')
    def _register_builtin_detectors(self):
        self._detectors.update(
            build_diagnose_gate_detectors(self._cycle_exempt_snapshot))
        missing = set(self._QUICK_RULE_IDS) - set(self._detectors)
        if missing:
            raise RuntimeError(
                f"_QUICK_RULE_IDS 含未注册规则: {sorted(missing)}")
    def _cycle_exempt_snapshot(self) -> set[tuple[str, str]]:
        return self.d01_cycle_exempt
    def check(self, code: str | None, filepath: str = '',
              tree: ast.AST | None = None) -> DiagnoseGateResult:
        return self._run_detectors(self._detectors, code, filepath, tree)
    def detector_modules(self) -> tuple:
        modules = {}
        for detector in self._detectors.values():
            module = inspect.getmodule(detector)
            if module is not None:
                modules[module.__name__] = module
        return tuple(modules[name] for name in sorted(modules))
    def _run_detectors(self, detectors: dict[str, Callable], code: str | None,
                       filepath: str, tree: ast.AST | None) -> DiagnoseGateResult:
        code, tree, early_result = _resolve_scan_tree(code, tree)
        if early_result is not None:
            return early_result
        if tree is None:
            return self._finalize([])
        issues: list[DiagnoseIssue] = []
        source_lines = aligned_source_lines(code)
        for check_id, detector_fn in detectors.items():
            try:
                result = detector_fn(code, tree, source_lines, filepath)
                findings = _iter_detector_findings(result)
                if findings is None:
                    issues.append(DiagnoseIssue(
                        check_id='GATE-DEGRADED',
                        severity=DiagnoseSeverity.ERROR,
                        message=(f'检测器 {check_id} 返回契约外结果'
                                 f'（{type(result).__name__}），本次检测未完成'),
                        line=0,
                        suggestion='检测器必须返回发现列表（dict 或带字段对象）'))
                    continue
                issues.extend(
                    _normalize_detector_issue(issue) for issue in findings)
            except Exception as exc:  # noqa: BLE001
                _log.warning('检测器 %s 执行异常, 降级为门禁错误', check_id,
                             exc_info=True)
                issues.append(DiagnoseIssue(
                    check_id='GATE-DEGRADED',
                    severity=DiagnoseSeverity.ERROR,
                    message=(f'检测器 {check_id} 执行异常'
                             f'（{type(exc).__name__}），本次检测未完成'),
                    line=0,
                    suggestion='修复检测器或其依赖后重试；严格门禁不得把未完成的检测视为通过'))
        return self._finalize(issues)
    def _finalize(self, issues: list[DiagnoseIssue]) -> DiagnoseGateResult:
        counts = _severity_counts(issues)
        block_count = counts[DiagnoseSeverity.BLOCK]
        error_count = counts[DiagnoseSeverity.ERROR]
        warn_count = counts[DiagnoseSeverity.WARN]
        ok = block_count == 0 and (not self.strict or error_count == 0)
        return DiagnoseGateResult(
            ok=ok, issues=issues,
            block_count=block_count, error_count=error_count,
            warn_count=warn_count,
            message=self._build_message(block_count, error_count, warn_count))
    def check_quick(self, code: str, filepath: str = '') -> DiagnoseGateResult:
        subset = {k: v for k, v in self._detectors.items()
                  if k in self._QUICK_RULE_IDS}
        return self._run_detectors(subset, code, filepath, None)
    def check_security_findings(
            self, security_findings: _SecurityFindings | None,
            filepath: str = '') -> DiagnoseGateResult:
        if security_findings is None:
            return self._finalize([])
        container_error = _security_findings_container_error(security_findings)
        if container_error is not None:
            _audit_blocked_security([container_error], filepath)
            return self._finalize([container_error])
        issues = self._consume_security_findings(security_findings, filepath)
        _audit_blocked_security(issues, filepath)
        return self._finalize(issues)
    def _consume_security_findings(
            self, findings: _SecurityFindings,
            filepath: str) -> list[DiagnoseIssue]:
        issues: list[DiagnoseIssue] = []
        for index, finding in enumerate(findings, 1):
            try:
                payload_error = _security_finding_payload_error(finding, index)
                if payload_error is not None:
                    issues.append(payload_error)
                    continue
                self._consume_one_security_finding(finding, filepath, issues)
            except Exception as exc:  # noqa: BLE001
                _log.warning("check_security_findings: 单条发现消费异常, 阻断该批次",
                             exc_info=True)
                issues.append(DiagnoseIssue(
                    check_id='SEC-INPUT', severity=DiagnoseSeverity.BLOCK,
                    message=(f'安全发现第 {index} 条消费异常'
                             f'（{type(exc).__name__}），无法安全消费'),
                    line=0,
                    suggestion='修复安全发现载荷或字段访问异常后重新提交'))
        return issues
    def _consume_one_security_finding(
            self, finding: object, filepath: str,
            issues: list[DiagnoseIssue]) -> None:
        if _finding_is_false_positive(finding):
            return
        sev_str = _finding_severity(finding)
        category_name = _finding_category(finding)
        cwe_id = _finding_field(finding, 'cwe_id', '')
        confidence = _finding_confidence(finding)
        source = _finding_field(finding, 'source', '')
        sink = _finding_field(finding, 'sink', '')
        suggestion = _finding_suggestion(finding)
        line = _finding_line(finding)
        gate_severity = self._finding_gate_severity(sev_str, confidence)
        issues.append(DiagnoseIssue(
            check_id=_finding_check_id(cwe_id, category_name),
            severity=gate_severity,
            message=_finding_message(category_name, sev_str, source, sink, cwe_id),
            line=line,
            suggestion=suggestion or '修复安全漏洞后重新提交',
            auto_fixable=False,
            details={'category': category_name, 'severity': sev_str,
                     'confidence': confidence, 'cwe_id': cwe_id,
                     'source': source, 'sink': sink,
                     'file': _finding_field(finding, 'file') or filepath}))
    def _finding_gate_severity(self, sev_str: str,
                                confidence: float) -> DiagnoseSeverity:
        gate_severity = _gate_enum_from_text(sev_str)
        if gate_severity is None:
            return DiagnoseSeverity.ERROR
        return (DiagnoseSeverity.INFO if confidence < 0.5
                else gate_severity)
    def check_with_security(
            self, code: str, security_findings: _SecurityFindings | None,
            filepath: str = '') -> DiagnoseGateResult:
        code_result = self.check(code, filepath)
        sec_result = self.check_security_findings(security_findings, filepath)
        merged_issues = code_result.issues + sec_result.issues
        return self._finalize(merged_issues)
    def _build_message(self, block: int, error: int, warn: int) -> str:
        parts = [f'{count} {label}'
                 for count, label in ((block, '阻断'), (error, '错误'), (warn, '警告'))
                 if count]
        return ','.join(parts) or '诊断通过'
class DiagnoseBlockedError(Exception):
    def __init__(self, result: DiagnoseGateResult):
        self.result = result
        super().__init__(f'DiagnoseGate 阻断: {result.message}')
_gate_cache: dict[bool, DiagnoseGate] = {}
def get_gate(strict: bool = DEFAULT_GATE_STRICT) -> DiagnoseGate:
    strict = signal_bool(strict)
    gate = _gate_cache.get(strict)
    if gate is None:
        gate = DiagnoseGate(strict=strict)
        _gate_cache[strict] = gate
    return gate
def to_gate_finding(iss: dict, fp: str) -> SimpleNamespace:
    return SimpleNamespace(
        is_false_positive=_finding_is_false_positive(iss),
        severity=iss.get("severity", _DEFAULT_FINDING_SEVERITY),
        category=SimpleNamespace(value=iss.get("category", "unknown")),
        cwe_id=iss.get("cwe_id", ""),
        confidence=iss.get("confidence", 1.0),
        source=iss.get("source", ""),
        sink=iss.get("sink", ""),
        suggestion=iss.get("suggestion", ""),
        line=iss.get("line", 0),
        file=iss.get("file") or fp,
    )
#: 设置 ``JWSGJ_AST_ASSERT=1`` 时，校验调用方传入的 ``tree`` 确实等于 ``ast.parse(code)``。
#: 结果缓存的正确性依赖「同 code 必得同 AST」这一不变式，此开关用于开发/回归期验证。
_AST_CONSISTENCY_ASSERT = os.environ.get("JWSGJ_AST_ASSERT", "") == "1"


def _assert_tree_matches_code(code: str, tree: Any) -> None:
    """开发期断言：传入的 AST 必须与源码重解析结果逐字等价。"""
    try:
        expected = ast.dump(ast.parse(code))
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'_assert_tree_matches_code:{type(_e).__name__}')
        return
    actual = ast.dump(tree)
    if actual != expected:  # pragma: no cover - 仅开发期断言
        raise AssertionError(
            "detect_all() 收到的 tree 与 code 重解析结果不一致；"
            "结果缓存以 code 为指纹，此不一致会导致错误命中")


def _ensure_tree(code: str, tree: Any) -> tuple[Any, BaseException | None]:
    if tree is not None:
        if _AST_CONSISTENCY_ASSERT:
            _assert_tree_matches_code(code, tree)
        return tree, None
    try:
        return ast.parse(code), None
    except PARSE_DEGRADE_EXC as _e:
        log_swallowed(__name__, _e,
                      context=f'_ensure_tree:{type(_e).__name__}')
        return None, _e
def load_source_and_tree(filepath: str, cache: Any = None) -> tuple[str | None, Any]:
    if cache is not None:
        try:
            source = cache.get_source(filepath)
        except Exception as _cache_exc:  # noqa: BLE001
            log_swallowed(
                __name__, _cache_exc,
                context=('load_source_and_tree:get_source:'
                         f'{type(_cache_exc).__name__}'))
            source = None
        if source is not None:
            try:
                return source, cache.get_ast(filepath)
            except Exception as _cache_exc:  # noqa: BLE001
                log_swallowed(
                    __name__, _cache_exc,
                    context=('load_source_and_tree:get_ast:'
                             f'{type(_cache_exc).__name__}'))
                return source, None
    source, _fingerprint = read_source_with_fingerprint(filepath)
    if source is None:
        _log.warning("源码读取失败，跳过文件: %s", filepath)
    return source, None
def _sorted_catalog(name: str) -> dict[str, Any]:
    catalog = detector_catalog(name)
    return {key: catalog[key] for key in sorted(catalog)}
def _diag4_direct_checks() -> dict[str, Any]:
    return _sorted_catalog("diag4_direct")
def _aicoder_direct_checks() -> dict[str, Any]:
    return _sorted_catalog("aicoder_direct")
def _rd_prevention_checks() -> dict[str, Any]:
    return {rid: fn for rid, fn in _diag4_direct_checks().items()
            if rid.startswith("RD-")}
def _new_pattern_detector_ids() -> tuple[tuple[str, type], ...]:
    return tuple(_sorted_catalog("new_pattern_classes").items())
_CATALOG_PROJECTIONS: dict[str, Callable[[], Any]] = {
    "DIAG4_DIRECT_CHECKS": _diag4_direct_checks,
    "RD_PREVENTION_CHECKS": _rd_prevention_checks,
    "AICODER_DIRECT_CHECKS": _aicoder_direct_checks,
}
def __getattr__(name: str) -> Any:
    projector = _CATALOG_PROJECTIONS.get(name)
    if projector is None:
        raise AttributeError(
            f"module {__name__!r} has no attribute {name!r}")
    return projector()
AUDIT_DETECTOR_IDS: tuple[str, ...] = (
    "D42", "D43", "D44", "D45", "D46",
    "D47", "D52", "D53", "D54", "D55",
)
_AUDIT_CHANNEL_CATALOG = "audit_detector_classes"
def _audit_classes() -> dict[str, type]:
    catalog = detector_catalog(_AUDIT_CHANNEL_CATALOG)
    missing = [did for did in AUDIT_DETECTOR_IDS if did not in catalog]
    if missing:
        raise KeyError(
            f"审计通道检测器目录缺族: {missing}（规则族自注册器未登记）")
    return {did: catalog[did] for did in AUDIT_DETECTOR_IDS}
def audit_detector_classes() -> tuple[tuple[str, type], ...]:
    return tuple(_audit_classes().items())
def audit_registry_class_ids() -> tuple[tuple[str, type], ...]:
    return tuple((did, cls) for did, cls in _audit_classes().items()
                 if not is_retired_rule(did))
def _source_text(source_lines) -> str | None:
    if isinstance(source_lines, str):
        return source_lines
    if not source_lines:
        return None
    chunks = [x if isinstance(x, str) else str(x) for x in source_lines]
    return "".join(
        chunk if index == len(chunks) - 1 or chunk.endswith(("\n", "\r"))
        else chunk + "\n"
        for index, chunk in enumerate(chunks))
def _capture_detector_output(detector_cls, run, filepath=""):
    findings: list = []
    try:
        raw = run()
        items = _iter_detector_findings(raw)
        if items is None:
            _log.warning(
                "[Detectors] %s 返回契约外结果（%s），标记降级",
                detector_cls.__name__, type(raw).__name__)
            return [_degraded_channel_issue(
                detector_cls.__name__,
                TypeError("检测器必须返回可迭代的发现序列"), filepath)]
        for f in items:
            if f is None:
                continue
            try:
                if isinstance(f, Mapping):
                    findings.append(dict(f))
                elif hasattr(f, 'to_dict'):
                    findings.append(f.to_dict())
                else:
                    findings.append(to_issue_dict(f, filepath))
            except Exception as item_exc:  # noqa: BLE001
                _log.warning(
                    "[Detectors] %s 单条发现序列化失败，已标记降级: %s",
                    detector_cls.__name__, item_exc, exc_info=True)
                findings.append(_degraded_channel_issue(
                    detector_cls.__name__, item_exc, filepath))
    except Exception as e:  # noqa: BLE001
        _log.warning("[Detectors] %s 执行失败，保留已产出的 %d 条并标记降级: %s",
                     detector_cls.__name__, len(findings), e, exc_info=True)
        findings.append(_degraded_channel_issue(
            detector_cls.__name__, e, filepath))
    return findings
class _DetectorInputs(NamedTuple):
    code: str | None
    tree: ast.AST | None
    source_lines: list[str]
    filepath: str
    @classmethod
    def resolve(cls, tree: ast.AST | None, source_lines,
                source_code: str | None, filepath: str) -> _DetectorInputs:
        code = (source_code if source_code is not None
                else _source_text(source_lines))
        if tree is not None and (
                code is None or (isinstance(code, str) and not code.strip())):
            code = ast.unparse(tree)
        if tree is None:
            if code is None and source_lines is None and filepath:
                code = _read_text_shared(filepath)
            tree = _ensure_tree(code, None)[0] if code else None
        if isinstance(filepath, (str, bytes, os.PathLike)):
            fp = os.fsdecode(os.fspath(filepath))
        else:
            fp = "" if filepath is None else str(filepath)
        return cls(code, tree, aligned_source_lines(code) if code else [], fp)
def _make_inputs_adapter(
        run: Callable[[_DetectorInputs], Any]) -> Callable[..., Any]:
    def _adapter(tree=None, source_lines=None, filepath="", source_code=None,
                 **_kwargs: Any) -> Any:
        return run(_DetectorInputs.resolve(tree, source_lines, source_code,
                                           filepath))
    return _adapter
def _make_class_detector_fn(detector_cls):
    def _run(inputs: _DetectorInputs) -> Any:
        if inputs.tree is None or inputs.code is None:
            return []
        d = detector_cls()
        _mem_path = inputs.filepath or f"<memory:{id(d):x}>"
        _had_memory_source = is_memory_source(_mem_path)
        _prev = read_py_source(_mem_path) if _had_memory_source else None
        register_memory_source(_mem_path, inputs.code)
        try:
            return _capture_detector_output(
                detector_cls, lambda: d.detect_file(_mem_path), inputs.filepath)
        finally:
            if _had_memory_source:
                register_memory_source(_mem_path, _prev or "")
            else:
                unregister_memory_source(_mem_path)
    _fn = _make_inputs_adapter(_run)
    _fn.__doc__ = f"{detector_cls.DETECTOR_ID}: {detector_cls.PATTERN_NAME}."
    return _fn
def _make_sec_detector_fn(check_fn):
    def _run(inputs: _DetectorInputs) -> Any:
        if inputs.tree is None:
            return []
        return check_fn(inputs.tree, inputs.source_lines, inputs.filepath)
    _fn = _make_inputs_adapter(_run)
    _fn.__doc__ = check_fn.__doc__
    return _fn
def make_gate_adapter(detect_fn: Callable, rule_id: str | None = None) -> Callable:
    def _run(inputs: _DetectorInputs) -> list:
        if inputs.tree is None:
            return []
        raw = detect_fn(inputs.code, inputs.tree, inputs.source_lines,
                        inputs.filepath)
        issues = _iter_detector_findings(raw)
        label = rule_id or getattr(detect_fn, "__name__", "gate_adapter")
        if issues is None:
            _log.warning(
                "[Detectors] 门禁适配器 %s 返回契约外结果（%s），标记降级",
                label, type(raw).__name__)
            return [_degraded_channel_issue(
                label, TypeError("检测器必须返回可迭代的发现序列"),
                inputs.filepath)]
        findings = []
        try:
            for i in issues:
                f = issue_to_finding(i, inputs.filepath)
                if rule_id:
                    f["rule_id"] = rule_id
                findings.append(f)
        except Exception as exc:  # noqa: BLE001
            _log.warning(
                "[Detectors] 门禁适配器 %s 结果消费失败，保留已产出的 %d 条并标记降级: %s",
                label, len(findings), exc, exc_info=True)
            findings.append(_degraded_channel_issue(
                label, exc, inputs.filepath))
        return findings
    return _make_inputs_adapter(_run)
_PROJECT_ROOT_MARKERS = (
    "pyproject.toml", "setup.py", "setup.cfg", "requirements.txt",
    "tox.ini", "SKILL.md", ".git",
)
_PROJECT_ROOT_MAX_CLIMB = 8
_WalkEntries = list[tuple[int, str, list[str]]]
_WALK_DIR_BUDGET = 2000
_LINES_CACHE_MAX = 2048
def _has_project_marker(dirpath: str) -> bool:
    try:
        return any(os.path.exists(os.path.join(dirpath, marker))
                   for marker in _PROJECT_ROOT_MARKERS)
    except OSError as _e:
        _log.debug("项目根标记探测失败(按无标记处理): %s: %s", dirpath, _e)
        return False
def _climb_package_chain(start: str) -> str:
    top = start
    for _ in range(_PROJECT_ROOT_MAX_CLIMB):
        if not os.path.isfile(os.path.join(top, "__init__.py")):
            break
        parent = os.path.dirname(top)
        if parent == top:
            break
        top = parent
    return top
def _project_root_of(filepath):
    if not filepath:
        return "."
    start = os.path.dirname(os.path.abspath(filepath))
    top = _climb_package_chain(start)
    probe = start
    while True:
        if _has_project_marker(probe):
            return probe
        if probe == top:
            break
        parent = os.path.dirname(probe)
        if parent == probe:
            break
        probe = parent
    probe = top
    for _ in range(_PROJECT_ROOT_MAX_CLIMB):
        parent = os.path.dirname(probe)
        if parent == probe:
            break
        probe = parent
        if _has_project_marker(probe):
            return probe
    return top
def _read_text_shared(fpath: str) -> str | None:
    content = read_shared_snapshot(fpath)
    if content is not None:
        return content
    content, _fingerprint = read_source_with_fingerprint(fpath)
    if content is None:
        _log.debug("上下文走查跳过不可读文件 %s", fpath)
    return content
def _relpath_depth(dirpath: str, root: str) -> int:
    _rel = os.path.relpath(dirpath, root)
    return 0 if _rel == os.curdir else _rel.count(os.sep) + 1
def _is_pruned_scan_dirname(name: str, skip: frozenset[str]) -> bool:
    return is_pruned_scan_dir(name, skip) or is_audit_skip_dir(name)
def _walk_budgeted(
    root: str, max_depth: int = 3
) -> Iterator[tuple[str, list[str], list[str]]]:
    skip = scan_prune_dirs(root)
    def _on_walk_error(exc: OSError) -> None:
        _log.warning("上下文走查目录失败，跳过该子树: %s", exc)
    for _visited, (dirpath, dirnames, filenames) in enumerate(
            os.walk(root, onerror=_on_walk_error), 1):
        if _visited > _WALK_DIR_BUDGET:
            _log.warning(
                "上下文走查目录预算耗尽(%d)，结果按已访问子集截断: %s",
                _WALK_DIR_BUDGET, root)
            return
        dirnames[:] = [d for d in dirnames
                       if not _is_pruned_scan_dirname(d, skip)]
        yield dirpath, dirnames, filenames
        if _relpath_depth(dirpath, root) >= max_depth:
            dirnames[:] = []
def _matches_any_pattern(text: str, patterns: list[str]) -> bool:
    for pattern in patterns:
        try:
            if re.search(pattern, text):
                return True
        except re.error as exc:
            _log.debug("上下文过滤正则模式非法，按不匹配处理: %r: %s",
                       pattern, exc)
    return False
@dataclass
class ContextRuleSet:
    known_frameworks: dict[str, list[str]] = field(default_factory=lambda: {
        "django": ["django", "DJANGO_SETTINGS_MODULE"],
        "flask": ["flask", "Flask(__name__)"],
        "fastapi": ["fastapi", "FastAPI("],
        "aiohttp": ["aiohttp", "aiohttp.web"],
        "starlette": ["starlette"],
        "sanic": ["sanic"],
        "tornado": ["tornado"],
        "pyramid": ["pyramid"],
        "bottle": ["bottle"],
    })
    framework_exemptions: dict[str, list[str]] = field(default_factory=lambda: {
        "django": [
            "mark_safe", "format_html", "conditional_escape",
            "reverse", "redirect", "HttpResponse",
        ],
        "flask": [
            "Markup", "escape", "url_for", "redirect",
            VULN_RENDER_TEMPLATE, "send_file",
        ],
        "fastapi": [
            "Depends", "Query", "Path", "Body",
            "HTTPException", "JSONResponse",
        ],
    })
    test_patterns: list[str] = field(default_factory=lambda: [
        r"(^|/)test_[^/]*\.py$", r"(^|/)[^/]*_test\.py$",
        r"(^|/)tests?/.*\.py$", r"(^|/)conftest\.py$",
        r"(^|/)fixtures?/.*\.py$",
    ])
    test_function_patterns: list[str] = field(default_factory=lambda: [
        r"^test_", r"^Test\w", r"Mock", r"Fake",
    ])
    safe_context_markers: list[str] = field(default_factory=lambda: [
        "# nosec", "# noqa", "# lint: disable",
        "# safetoken: ok",
    ])
    path_exemptions: list[str] = field(default_factory=lambda: [
        "setup.py", "conftest.py",
        "migrations/", "alembic/",
    ])
    def add_framework_exemption(self, framework: str, patterns: list[str]) -> None:
        self.framework_exemptions.setdefault(framework, []).extend(patterns)
    def add_path_exemption(self, pattern: str) -> None:
        self.path_exemptions.append(pattern)
class ContextExtractor:
    def __init__(self, rule_set: ContextRuleSet | None = None):
        self.rules = rule_set or ContextRuleSet()
    def extract(self, project_root: str) -> ProjectContext:
        try:
            root = os.fsdecode(os.fspath(project_root)) if project_root else ""
        except (TypeError, ValueError):
            root = ""
        if not root or not os.path.isdir(root):
            raise ValueError(f"项目根不存在或不是目录: {project_root!r}")
        ctx = ProjectContext()
        walk_entries, marker_texts = self._scan_project_snapshot(root)
        for fw_name, markers in self.rules.known_frameworks.items():
            if self._match_markers_shared(marker_texts, markers):
                ctx.frameworks.append(fw_name)
        ctx.project_type = self._classify_project_type(
            walk_entries, ctx.frameworks)
        ctx.has_tests = (self._has_directory(root, "tests")
                         or self._has_directory(root, "test")
                         or self._has_tests_shared(walk_entries))
        ctx.has_ci = self._has_file_pattern(root, [".github", ".gitlab-ci.yml", "Jenkinsfile", ".circleci"])
        ctx.has_type_checking = self._has_file_pattern(root, ["mypy.ini", "pyproject.toml"])
        _log.info(
            "上下文提取完成: type=%s, frameworks=%s, has_tests=%s, has_ci=%s, type_checking=%s",
            ctx.project_type, ctx.frameworks, ctx.has_tests, ctx.has_ci, ctx.has_type_checking,
        )
        return ctx
    def _classify_project_type(
            self, walk_entries: _WalkEntries,
            frameworks: list[str]) -> str:
        if frameworks:
            return "web"
        if self._has_entry_points_shared(walk_entries):
            return "cli"
        if self._has_notebook_shared(walk_entries):
            return "datascience"
        return "library"
    def _scan_project_snapshot(
        self, root: str
    ) -> tuple[_WalkEntries, dict[str, str]]:
        walk_entries: _WalkEntries = []
        marker_texts: dict[str, str] = {}
        for dirpath, _dirnames, filenames in _walk_budgeted(root, max_depth=3):
            relative_dir = os.path.relpath(dirpath, root).replace(os.sep, "/")
            if relative_dir == os.curdir:
                relative_dir = ""
            walk_entries.append((
                _relpath_depth(dirpath, root), relative_dir, filenames))
            self._collect_marker_files(dirpath, filenames, marker_texts)
        return walk_entries, marker_texts
    @staticmethod
    def _collect_marker_files(
            dirpath: str, filenames: list[str],
            marker_texts: dict[str, str]) -> None:
        for fname in filenames:
            if not _is_source_marker(fname):
                continue
            fpath = os.path.join(dirpath, fname)
            content = _read_text_shared(fpath)
            if content is not None:
                marker_texts[fpath] = content.lower()
    @staticmethod
    def _match_markers_shared(
        marker_texts: dict[str, str], markers: list[str]
    ) -> bool:
        lowered = tuple(map(str.lower, markers))
        return any(
            marker in content_lower
            for content_lower in marker_texts.values()
            for marker in lowered
        )
    def _has_tests_shared(self, walk_entries: _WalkEntries) -> bool:
        return any(
            _matches_any_pattern(
                f"{relative_dir}/{filename}" if relative_dir else filename,
                self.rules.test_patterns)
            for _depth, relative_dir, filenames in walk_entries
            for filename in filenames
        )
    def _has_entry_points_shared(self, walk_entries: _WalkEntries) -> bool:
        return any(
            "__main__.py" in filenames
            for _depth, _relative_dir, filenames in walk_entries)
    def _has_notebook_shared(self, walk_entries: _WalkEntries) -> bool:
        return any(
            depth <= 3 and any(
                fname.lower().endswith(".ipynb") for fname in filenames)
            for depth, _relative_dir, filenames in walk_entries
        )
    def _has_directory(self, root: str, dirname: str) -> bool:
        return os.path.isdir(os.path.join(root, dirname))
    def _has_file_pattern(self, root: str, patterns: list[str]) -> bool:
        return any(os.path.exists(os.path.join(root, pattern)) for pattern in patterns)
class ContextAwareFilter:
    def __init__(self, context: ProjectContext, rule_set: ContextRuleSet):
        self.context = context
        self.rules = rule_set
        self._lines_cache: dict[str, tuple[
            list[str], dict[int, tuple[str, ...]]]] = {}
    def should_filter(self, finding: dict[str, Any], filepath: str) -> bool:
        if finding_rule_id(finding) == "GATE-DEGRADED":
            return False
        if (self._is_path_exempt(filepath)
                and not _is_security_finding(finding)
                and not _is_high_severity_finding(finding)):
            return True
        if self._is_test_code(filepath, finding):
            return True
        if self._has_safe_marker(filepath, finding):
            return True
        if _is_security_finding(finding) or _is_high_severity_finding(finding):
            return False
        return self._is_framework_exempt(finding)
    def _is_path_exempt(self, filepath: str) -> bool:
        rp = filepath.replace("\\", "/").strip("/")
        if not rp:
            return False
        _parts = rp.split("/")
        _haystack = "/" + rp + "/"
        for pattern in self.rules.path_exemptions:
            norm = str(pattern).replace("\\", "/").strip().strip("/")
            if not norm or norm == ".":
                continue
            norm = norm.removeprefix("./")
            if norm in _parts or "/" + norm + "/" in _haystack:
                return True
        return False
    def _is_test_code(self, filepath: str, finding: dict[str, Any]) -> bool:
        rp = filepath.replace("\\", "/")
        if _matches_any_pattern(rp, self.rules.test_patterns):
            return True
        func_name = _finding_text(
            finding.get("function") or finding.get("name") or "")
        return _matches_any_pattern(
            func_name, self.rules.test_function_patterns)
    def _load_file_snapshot(
            self, filepath: str,
    ) -> tuple[list[str], dict[int, tuple[str, ...]]] | None:
        snapshot = self._lines_cache.get(filepath)
        if snapshot is not None:
            return snapshot
        content = _read_text_shared(filepath)
        if content is None:
            _log.debug("safe_marker 读取失败，跳过该行标记检查 %s", filepath)
            return None
        lines = aligned_source_lines(content)
        tokens = comment_tokens(content)
        comments: dict[int, list[str]] = {}
        for token in tokens or ():
            comments.setdefault(token.start[0], []).append(token.string)
        snapshot = (lines, {
            line: tuple(items) for line, items in comments.items()})
        bounded_cache_put(self._lines_cache, filepath, snapshot,
                          _LINES_CACHE_MAX)
        return snapshot
    def _has_safe_marker(self, filepath: str, finding: dict[str, Any]) -> bool:
        if not filepath or not os.path.isfile(filepath):
            return False
        line_no = _finding_line(finding)
        if not line_no:
            return False
        snapshot = self._load_file_snapshot(filepath)
        if snapshot is None:
            return False
        lines, comments = snapshot
        if not lines or line_no > len(lines):
            return False
        return any(
            self._comment_has_marker(comment)
            for comment in comments.get(line_no, ())
        )
    def _comment_has_marker(self, comment: str) -> bool:
        return any(
            re.search(rf"{re.escape(marker)}(?![\w-])", comment)
            for marker in self.rules.safe_context_markers
        )
    def _is_framework_exempt(self, finding: dict[str, Any]) -> bool:
        if not self.context.frameworks:
            return False
        msg_lower = _finding_text(finding.get("message", "")).lower()
        return any(
            self._framework_message_hit(fw, msg_lower)
            for fw in self.context.frameworks
        )
    def _framework_message_hit(self, framework: str, msg_lower: str) -> bool:
        if framework.lower() in msg_lower:
            return True
        return any(
            ex.lower() in msg_lower
            for ex in self.rules.framework_exemptions.get(framework, [])
        )
def _normalize_finding(finding: Any) -> dict[str, Any]:
    if isinstance(finding, dict):
        return finding
    if isinstance(finding, Mapping):
        return dict(finding)
    result: dict[str, Any] = {}
    for attr in ("message", "line", "lineno", "severity", "level",
                 "rule_id", "check_id", "function", "name", "dimension",
                 "category", "code"):
        if hasattr(finding, attr):
            result[attr] = getattr(finding, attr)
    return result
def _filter_findings(
        filter_: ContextAwareFilter, findings: list, filepath: str) -> list:
    items = findings if isinstance(findings, list) else list(findings)
    filtered = [
        f for f in items
        if not filter_.should_filter(_normalize_finding(f), filepath)
    ]
    removed = len(items) - len(filtered)
    if removed:
        _log.info(
            "上下文感知过滤: %s 移除 %d/%d 项发现",
            filepath, removed, len(items),
        )
    return filtered
def quick_context_extract(project_root: str) -> ProjectContext:
    return ContextExtractor().extract(project_root)
def quick_context_filter(
    findings: list,
    filepath: str,
    project_root: str,
    context: ProjectContext | None = None,
) -> list:
    rules = ContextRuleSet()
    if context is None:
        context = ContextExtractor(rules).extract(project_root)
    return _filter_findings(ContextAwareFilter(context, rules), findings, filepath)
_PROJECT_CONTEXT_CACHE: dict = {}
_PROJECT_CONTEXT_MAX = 16
_PROJECT_CONTEXT_MISS = object()
def _is_source_marker(name: str) -> bool:
    lowered = str(name).lower()
    return lowered.endswith((".py", ".toml")) or lowered == "requirements.txt"
def _shallow_has_source(abs_root: str) -> bool:
    if not os.path.isdir(abs_root):
        raise OSError(f"项目根不存在或不是目录: {abs_root}")
    return any(
        any(_is_source_marker(name) for name in filenames)
        for _depth, _dirnames, filenames in _walk_budgeted(abs_root,
                                                            max_depth=2)
    )
def bounded_cache_put(cache: dict, key: Any, value: Any, max_size: int) -> None:
    if max_size <= 0:
        cache.clear()
        return
    if len(cache) >= max_size:
        cache.clear()
    cache[key] = value
def _extract_project_context(abs_root: str):
    try:
        return quick_context_extract(abs_root)
    except (OSError, ValueError, RuntimeError) as _ctx_e:
        _log.warning("项目上下文提取失败: %s", _ctx_e)
        return None
def _get_cached_project_context(project_root: str):
    abs_root = os.path.abspath(project_root) if project_root else os.path.abspath(".")
    cached = _PROJECT_CONTEXT_CACHE.get(abs_root, _PROJECT_CONTEXT_MISS)
    if cached is not _PROJECT_CONTEXT_MISS:
        return cached
    try:
        has_source = _shallow_has_source(abs_root)
    except (OSError, ValueError) as _e:
        _log.debug("项目上下文探测失败(返回 None): %s (%s)", abs_root, _e)
        return None
    if not has_source:
        bounded_cache_put(_PROJECT_CONTEXT_CACHE, abs_root, None,
                          _PROJECT_CONTEXT_MAX)
        return None
    ctx = _extract_project_context(abs_root)
    bounded_cache_put(_PROJECT_CONTEXT_CACHE, abs_root, ctx, _PROJECT_CONTEXT_MAX)
    return ctx
def clear_project_context_cache() -> None:
    _PROJECT_CONTEXT_CACHE.clear()
def _acquire_project_context(filepath: Any) -> tuple[Any, Any]:
    try:
        _root = _project_root_of(filepath)
        return _root, _get_cached_project_context(_root)
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError) as e:
        _log.warning("context extraction failed: %s", e)
        return ".", None
def _filter_with_context(all_issues: Any, filepath: Any, project_root: Any,
                         project_context: Any) -> Any:
    if not (project_context and all_issues):
        return all_issues
    try:
        return quick_context_filter(all_issues, filepath, project_root,
                                    context=project_context)
    except (AttributeError, KeyError, TypeError, ValueError, RuntimeError, NameError) as e:
        _log.warning("context filter failed: %s", e)
        return all_issues
def filter_findings_with_context(all_issues: Any, filepath: Any) -> Any:
    if not all_issues:
        return all_issues
    try:
        _fp = os.fsdecode(os.fspath(filepath)) if filepath else ""
    except (TypeError, ValueError):
        _fp = ""
    if not _fp or not os.path.isfile(_fp):
        return all_issues
    project_root, project_context = _acquire_project_context(_fp)
    return _filter_with_context(all_issues, _fp, project_root,
                                project_context)
def _finding_text(value: Any) -> str:
    return value if isinstance(value, str) else ""
def _is_security_finding(finding: dict[str, Any]) -> bool:
    for key in ("category", "dimension"):
        value = _carrier_value(finding.get(key))
        if isinstance(value, str) and value.strip().lower() == "security":
            return True
    return category_from_rule_id(finding_rule_id(finding)) == "security"
def _is_high_severity_finding(finding: dict[str, Any]) -> bool:
    severity = finding.get("severity")
    if severity is None or severity == "":
        severity = finding.get("level")
    text = severity_text_value(severity)
    if text is None:
        return False
    return normalize_severity(text) in ("P0", "P1")
def _class_detector_bindings(
        entries: tuple[tuple[str, type], ...],
) -> tuple[dict[str, Callable], int]:
    bindings: dict[str, Callable] = {}
    failed = 0
    for check_id, detector_cls in entries:
        try:
            bindings[check_id] = _make_class_detector_fn(detector_cls)
        except Exception as _bind_exc:  # noqa: BLE001
            failed += 1
            _log.warning("[Detectors] %s 接线失败，仅跳过该规则: %s",
                         check_id, _bind_exc, exc_info=True)
    return bindings, failed
def _register_to_detector_registry() -> tuple[int, int]:
    entries = _new_pattern_detector_ids()
    bindings, failed = _class_detector_bindings(entries)
    registered, install_failed = _install_direct_bindings(
        bindings,
        "new pattern detectors registered to DetectorRegistry: "
        f"{[check_id for check_id, _cls in entries]}")
    return registered, failed + install_failed
def _register_audit_patterns() -> tuple[int, int]:
    entries = audit_registry_class_ids()
    bindings, failed = _class_detector_bindings(entries)
    registered, install_failed = _install_direct_bindings(
        bindings,
        f"audit pattern detectors registered to DetectorRegistry: "
        f"{[check_id for check_id, _cls in entries]}")
    return registered, failed + install_failed
_GATE_RULE_CATALOG: dict[str, Callable[..., Any]] | None = None
def _gate_rule_catalog() -> dict[str, Callable[..., Any]]:
    global _GATE_RULE_CATALOG
    if _GATE_RULE_CATALOG is None:
        catalog: dict[str, Callable[..., Any]] = {}
        for module_name in GATE_RULE_MODULES:
            module = importlib.import_module(module_name)
            provided = getattr(module, "GATE_DETECTORS", None)
            if not isinstance(provided, dict) or not provided:
                raise RuntimeError(
                    f"门禁规则族 {module_name} 未提供非空 "
                    "GATE_DETECTORS 规则目录")
            duplicates = sorted(catalog.keys() & provided.keys())
            if duplicates:
                raise RuntimeError(
                    f"门禁规则族 {module_name} 重复提供规则 ID: "
                    f"{', '.join(duplicates)}")
            catalog.update(provided)
        _GATE_RULE_CATALOG = catalog
    return _GATE_RULE_CATALOG
def build_diagnose_gate_detectors(
    cycle_exempt: Callable[[], set[tuple[str, str]]],
) -> dict[str, Callable]:
    _d01_detect = detector_catalog("gate_bindings")["D01"]
    def _d01_bound(code, tree, source_lines=None, filepath=""):
        return _d01_detect(
            code, tree, source_lines, filepath,
            d01_cycle_exempt=cycle_exempt())
    catalog = _gate_rule_catalog()
    if "D01" in catalog:
        raise RuntimeError("门禁规则族目录不得覆盖实例级 D01 检测器")
    return {"D01": _d01_bound, **catalog}
def _register_sec_family() -> tuple[int, int]:
    bindings: dict[str, Callable] = {}
    failed = 0
    for cid, fn in _sorted_catalog("sec_registry_fns").items():
        try:
            bindings[cid] = _make_sec_detector_fn(fn)
        except Exception as _sec_exc:  # noqa: BLE001
            failed += 1
            _log.warning(
                "[Detectors] 安全族 %s 接线失败，仅跳过该规则: %s",
                cid, _sec_exc, exc_info=True)
    registered, install_failed = _install_direct_bindings(
        bindings, f"security registry family ({len(bindings)}) registered")
    return registered, failed + install_failed
def registry_sec_family_ids() -> frozenset:
    return frozenset(
        cid for cid, fn in _sorted_catalog("sec_registry_fns").items()
        if cid.startswith("SE") and cid[2:].isdigit()
        and fn.__name__ == f"check_{cid}"
    )
_GATE_ADAPTER_CATALOG = "gate_adapter_bindings"
def _register_rb_check() -> tuple[int, int]:
    adapters = detector_catalog(_GATE_ADAPTER_CATALOG)
    bindings: dict[str, Callable] = {}
    failed = 0
    for alias, spec in adapters.items():
        try:
            detect, gate_rule_id = spec
        except (TypeError, ValueError) as _spec_exc:
            failed += 1
            _log.warning(
                "[Detectors] 门禁适配器登记项 %s 形态非法，仅跳过该条: %s",
                alias, _spec_exc)
            continue
        bindings[alias] = make_gate_adapter(detect, rule_id=gate_rule_id)
    registered, install_failed = _install_direct_bindings(
        bindings, f"gate adapter bindings ({len(bindings)}) registered")
    return registered, failed + install_failed
def _install_direct_bindings(bindings: dict[str, Any],
                              log_message: str) -> tuple[int, int]:
    registry = get_registry()
    registered = 0
    failed = 0
    for check_id, fn in bindings.items():
        try:
            registry.register(check_id, fn)
            registered += 1
        except Exception as _bind_exc:  # noqa: BLE001
            failed += 1
            _log.warning(
                "[Detectors] 检测器绑定失败，仅跳过该规则: %s: %s",
                check_id, _bind_exc, exc_info=True)
    _log.debug("%s（成功 %d / 失败 %d）", log_message, registered, failed)
    return registered, failed
def _register_recovered_check() -> tuple[int, int]:
    bindings = _sorted_catalog("recovered_bindings")
    return _install_direct_bindings(
        bindings,
        f"recovered legacy rule detectors ({len(bindings)}) registered to DetectorRegistry")
def _register_traps_check() -> tuple[int, int]:
    bindings = _sorted_catalog("traps_bindings")
    return _install_direct_bindings(
        bindings,
        f"trap/boundary legacy rule detectors ({len(bindings)}) registered to DetectorRegistry")
def _register_rule_bindings() -> tuple[int, int]:
    bindings = _sorted_catalog("rule_bindings")
    registered, failed = _install_direct_bindings(
        bindings,
        f"general rule bindings ({len(bindings)}) registered to DetectorRegistry")
    _log.info("通用规则族规则绑定注册完成: %d 项（失败 %d）", registered, failed)
    return registered, failed
@lru_cache(maxsize=1)
def _wiring_module_objects() -> tuple[Any, ...]:
    return tuple(
        importlib.import_module(name) for name in WIRING_MODULES
    )
_CATALOG_REGISTRAR_NAME = "_register_detector_catalogs"
_global_registered: bool = False
_registration_lock = threading.Lock()
def _is_zero_arg_registrar(fn: Any) -> bool:
    try:
        signature = inspect.signature(fn)
    except (TypeError, ValueError) as _sig_err:
        _log.debug("[Aggregation] 签名不可检查，按非零参注册器处理: %s: %s",
                   type(fn).__name__, _sig_err)
        return False
    return all(
        param.default is not param.empty
        or param.kind in (param.VAR_POSITIONAL, param.VAR_KEYWORD)
        for param in signature.parameters.values()
    )
def _collect_register_fns(pairs: Any) -> list[tuple[str, Any]]:
    return [
        (name, fn) for name, fn in pairs
        if name.startswith('_register')
        and callable(fn)
        and _is_zero_arg_registrar(fn)
    ]
def ensure_wirings_registered() -> None:
    global _global_registered
    if _global_registered or getattr(init_reentrant, "active", False):
        return
    with _registration_lock:
        if _global_registered or getattr(init_reentrant, "active", False):
            return
        init_reentrant.active = True
        try:
            failed = _run_detector_registration()
        except BaseException:
            _global_registered = False
            raise
        else:
            _global_registered = failed == 0
        finally:
            init_reentrant.active = False
def _wiring_declaration(mod: Any) -> dict[str, Any]:
    provider = getattr(mod, WIRING_DECLARATION_ATTR, None)
    if not callable(provider):
        return {}
    declared = provider()
    return declared if isinstance(declared, dict) else {}
def _merge_declared_wiring() -> int:
    failed = 0
    for _mod in _wiring_module_objects():
        try:
            declared = _wiring_declaration(_mod)
            for _name, _entries in (declared.get("catalogs") or {}).items():
                if isinstance(_entries, dict) and _entries:
                    register_detector_catalog(_name, dict(_entries))
            for _label, _hook in (declared.get("rebuild_hooks") or {}).items():
                if callable(_hook):
                    register_rebuild_hook(_label, _hook)
            _registry_bindings = declared.get("registry") or {}
            if isinstance(_registry_bindings, dict):
                _registered, binding_failed = _install_direct_bindings(
                    dict(_registry_bindings),
                    f"declared registry bindings: "
                    f"{getattr(_mod, '__name__', _mod)}")
                failed += binding_failed
        except Exception:  # noqa: BLE001
            failed += 1
            _log.warning("Declared wiring of %s failed",
                         getattr(_mod, "__name__", _mod), exc_info=True)
    return failed
def _run_detector_registration() -> int:
    _log.info("Auto-registering detectors to DetectorRegistry...")
    registry = get_registry()
    failed = _merge_declared_wiring()
    count_before = len(registry.list_registered())
    register_fns = _discover_register_fns()
    succeeded, registrar_failed = _invoke_register_fns(register_fns)
    failed += registrar_failed
    count_after = len(registry.list_registered())
    _log.info(
        "Detectors registered: %d -> %d (+%d) | %d succeeded, %d failed, %d total fns",
        count_before, count_after, count_after - count_before,
        succeeded, failed, len(register_fns),
    )
    return failed
def _discover_register_fns() -> list[tuple[str, Any]]:
    register_fns: list[tuple[str, Any]] = []
    for _mod in _wiring_module_objects():
        register_fns.extend(_collect_register_fns(list(vars(_mod).items())))
    register_fns.extend(_collect_register_fns(list(globals().items())))
    register_fns.sort(
        key=lambda pair: (pair[0] != _CATALOG_REGISTRAR_NAME, pair[0]))
    return register_fns
def _invoke_register_fns(register_fns: list[tuple[str, Any]]) -> tuple[int, int]:
    succeeded = 0
    failed = 0
    for name, fn in register_fns:
        try:
            result = fn()
            succeeded += 1
            if (isinstance(result, tuple) and len(result) == 2
                    and all(isinstance(value, int)
                            and not isinstance(value, bool) for value in result)):
                failed += result[1]
        except Exception:  # noqa: BLE001
            _log.warning("Detector registration %s failed", name, exc_info=True)
            failed += 1
    return succeeded, failed
def _reset_wirings_registration() -> None:
    global _global_registered
    with _registration_lock:
        _global_registered = False
register_review_provider("precreation_review_gate", DiagnoseGate)
set_auto_register_hook(ensure_wirings_registered)
set_registry_reset_hook(_reset_wirings_registration)
_SERIES_RE_B = re.compile(r"^B\d{1,2}$")
_SERIES_RE_O = re.compile(r"^O\d{1,2}$")
_SYNTAX_ERROR_CHECK_ID = "D29"
class _SeriesSpec(NamedTuple):
    check_name: str
    series_re: re.Pattern
    skip_message: str
    none_message: str
    found_message: str
    dynamic_blocking: bool
@lru_cache(maxsize=8)
def _scan_antipatterns_shared(content: str):
    return DiagnoseGate(strict=True).check(content, "")
def _series_result(check_name: str, passed: bool, severity: str, message: str,
                  details: list | None = None,
                  suggestions: list | None = None) -> PreinterventionResult:
    return PreinterventionResult(
        check_name=check_name, passed=passed, severity=severity,
        message=message, details=details or [], suggestions=suggestions or [])
def _gate_series_result(content: str, spec: _SeriesSpec) -> PreinterventionResult:
    name = spec.check_name
    content = normalize_input(
        content, f"check_{name.removesuffix('_check')} 参数 content")
    if not content.strip():
        return _series_result(name, True, SEVERITY_INFO, spec.skip_message)
    scan_issues = _scan_antipatterns_shared(content).issues
    syntax_result = _gate_syntax_error_result(name, scan_issues)
    if syntax_result is not None:
        return syntax_result
    degraded = [i for i in scan_issues if i.check_id == "GATE-DEGRADED"]
    if degraded:
        details, suggestions, _has_blocking = _gate_series_findings(
            degraded, True)
        return _series_result(
            name, False, SEVERITY_BLOCKING,
            f"{len(degraded)} 个检测器未完成检查，无法判定结果",
            details, suggestions)
    issues = [i for i in scan_issues if spec.series_re.match(i.check_id)]
    if not issues:
        return _series_result(name, True, SEVERITY_INFO, spec.none_message)
    details, suggestions, has_blocking = _gate_series_findings(
        issues, spec.dynamic_blocking)
    severity = SEVERITY_BLOCKING if has_blocking else SEVERITY_WARNING
    return _series_result(name, False, severity,
                          spec.found_message.format(len(issues)),
                          details, suggestions)
def _gate_syntax_error_result(check_name: str,
                              scan_issues: list) -> PreinterventionResult | None:
    syntax_errors = [i for i in scan_issues
                     if i.check_id == _SYNTAX_ERROR_CHECK_ID]
    if not syntax_errors:
        return None
    err = syntax_errors[0]
    return PreinterventionResult(
        check_name=check_name, passed=False, severity=SEVERITY_BLOCKING,
        message=err.message,
        details=[make_detail(
            issue=f"[{err.check_id}] {err.message}",
            rule_id=err.check_id,
            locator=f"line:{err.line}",
            confidence=1.0,
        )],
        suggestions=[err.suggestion] if err.suggestion else [],
    )
def _gate_series_findings(issues: list,
                          dynamic_blocking: bool) -> tuple[list, list, bool]:
    return collect_findings(
        (f"[{issue.check_id}] {issue.message}", issue.check_id,
         f"line:{issue.line}", issue.suggestion,
         bool(dynamic_blocking
              and getattr(issue.severity, "value", issue.severity)
              in ("BLOCK", "ERROR")))
        for issue in issues)
_BUG_SERIES = _SeriesSpec(
    check_name="bug_antipatterns_check",
    series_re=_SERIES_RE_B,
    skip_message="未提供代码内容，跳过 BUG 反模式检查",
    none_message="未发现 BUG 类反模式",
    found_message="发现 {} 个 BUG 类反模式",
    dynamic_blocking=True,
)
_OVER_ENGINEERING_SERIES = _SeriesSpec(
    check_name="over_engineering_check",
    series_re=_SERIES_RE_O,
    skip_message="未提供代码内容，跳过过度设计检查",
    none_message="未发现过度设计反模式",
    found_message="发现 {} 个过度设计信号",
    dynamic_blocking=False,
)
def check_bug_antipatterns(content: str = "") -> PreinterventionResult:
    return _gate_series_result(content, _BUG_SERIES)
def check_over_engineering(content: str = "") -> PreinterventionResult:
    return _gate_series_result(content, _OVER_ENGINEERING_SERIES)
def _series_check_provider() -> dict:
    return {
        "bug_antipatterns_check": check_bug_antipatterns,
        "over_engineering_check": check_over_engineering,
    }
register_check_provider(_series_check_provider)
_DETECT_CACHE: dict = {}
_DETECT_CACHE_MAX = 512
def _normalize_detect_input(code: Any, tree: Any) -> tuple[str, bool]:
    if tree is not None and not isinstance(tree, ast.Module):
        raise TypeError(
            "detect_all() 的 tree 必须是 ast.Module"
            f"（实际 {type(tree).__name__}）")
    if isinstance(code, str):
        if tree is not None and not code.strip():
            return ast.unparse(tree), True
        return code, False
    if tree is not None:
        return ast.unparse(tree), True
    raise TypeError(
        "detect_all() 需要源码字符串（code: str）；"
        "已解析 AST 请经 tree 参数传入")
def _get_cache_key(code: str, filepath: str,
                   exclude_rules: Any = None) -> tuple:
    """生成 detect_all 结果缓存键。

    三个维度缺一不可：

    * ``path_text``：同一份源码落在不同路径下，部分规则的基线/白名单结论不同；
    * ``code``：源码文本本身就是内容指纹，同 ``code`` 必得同 ``AST`` 必得同结论；
    * ``exclude_rules``：排除集不同则输出集合不同（生产恒传 182 条退役规则）。

    历史教训：旧实现把 ``exclude_rules`` 与 ``has_tree`` 当成“禁用缓存”的闸门，
    而生产调用方 ``_scan_file_and_registry`` 恒传 ``tree=_tree`` 且恒传非空
    ``exclude_rules``，两个条件均为真，导致结果缓存**从未命中过一次**——
    同一文件被多个子系统反复全量扫描（重复劳动/重复遍历的直接来源）。
    正确做法是把维度并入键，而不是关掉缓存。
    """
    try:
        path_text = os.path.normcase(os.path.abspath(
            os.fsdecode(os.fspath(filepath))))
    except (TypeError, ValueError):
        path_text = str(filepath)
    try:
        exclude_key: Any = (frozenset(exclude_rules)
                            if exclude_rules else frozenset())
    except TypeError:
        exclude_key = tuple(sorted(str(r) for r in exclude_rules or ()))
    # 源码以摘要入键：直接存文本会使 512 个条目常驻上百 MB 源码副本。
    # 摘要算法固定为 sha256，进程内稳定；同文本必得同摘要。
    digest = hashlib.sha256(code.encode("utf-8", "surrogatepass")).hexdigest()
    return (path_text, digest, exclude_key)
def _detect_cache_gate(code: Any, filepath: Any, exclude_rules: Any,
                       degraded: bool) -> tuple[bool, Any]:
    """判断本次 detect_all 调用能否复用结果缓存，并给出缓存键。

    缓存键由 ``_get_cache_key`` 生成，已完整覆盖「路径 + 源码 + 排除集」三个
    决定输出的维度，故只需排除两类确实无法作指纹的情形：

    * ``filepath`` 为空：无路径上下文，无法与其他调用区分；
    * ``degraded``：``code`` 是由 ``ast.unparse(tree)`` 反推出来的（原调用方只给
      了 AST 没给源码），此时 ``code`` 不是真实源码，不能作指纹。
    """
    if degraded or not filepath:
        return False, None
    return True, _get_cache_key(code, filepath, exclude_rules)
def _load_cached_result(cache_key: tuple) -> list | None:
    _cached = _DETECT_CACHE.get(cache_key)
    return copy.deepcopy(_cached) if _cached is not None else None
def _store_cached_result(cache_key: tuple, result: list) -> None:
    bounded_cache_put(_DETECT_CACHE, cache_key, copy.deepcopy(result),
                      _DETECT_CACHE_MAX)
def _syntax_error_findings(code: Any, filepath: Any, exclude_rules: Any,
                            _e: BaseException, skill_dir: Any = "") -> list:
    _syntax_head = to_issue_dict({"rule_id": "SYNTAX", "message": str(_e),
                                  "severity": "CRITICAL"}, filepath,
                                 skill_dir=skill_dir)
    try:
        _run_gf, _gf_post_exclude = early_channel("GF")
    except KeyError as _gf_exc:
        _log.warning("[Detectors] GF 早期通道未登记，语法错误路径跳过 GF 发现: %s",
                     _gf_exc)
        _gf_issues: list = []
    else:
        _gf_raw = _run_channel_checked(
            "GF",
            lambda: _invoke_early_channel(
                _run_gf, code, None, None, filepath, exclude_rules),
            filepath, skill_dir)
        _gf_issues = []
        _extend_detector_channel_issues(
            _gf_issues, _gf_raw, "GF", filepath, skill_dir)
        if _gf_post_exclude:
            _gf_issues = _filter_excluded_issues(_gf_issues, exclude_rules)
    return [_syntax_head, *deduplicate_issues(apply_suppress_filter(
        _gf_issues, code))]
def detect_all(code: Any, filepath: str = "", *, tree: Any = None,
               exclude_rules: Any = None) -> Any:
    code, _degraded_source = _normalize_detect_input(code, tree)
    exclude_rules = _normalize_exclude_rules(exclude_rules)
    _use_cache, _cache_key = _detect_cache_gate(code, filepath, exclude_rules,
                                                _degraded_source)
    if _use_cache:
        _cached = _load_cached_result(_cache_key)
        if _cached is not None:
            return _cached
    project_root = (_project_root_of(filepath)
                    if filepath and os.path.isfile(os.fspath(filepath)) else "")
    tree, _parse_error = _ensure_tree(code, tree)
    if _parse_error is not None:
        _log.warning(MSG_SYNTAX_ERROR_SKIP)
        return _syntax_error_findings(code, filepath, exclude_rules, _parse_error,
                                      skill_dir=project_root)
    source_lines = aligned_source_lines(code)
    all_issues: list = []
    _phase_early_checks(all_issues, code, tree, source_lines, filepath,
                        exclude_rules, skill_dir=project_root)
    _phase_security_checks(all_issues, tree, source_lines, filepath,
                           exclude_rules, skill_dir=project_root)
    try:
        engines = engine_channels()
    except Exception as _engines_exc:  # noqa: BLE001
        _log.warning("引擎检查通道目录不可用，已标记降级: %s",
                     _engines_exc, exc_info=True)
        all_issues.append(_degraded_channel_issue(
            "engine_catalog", _engines_exc, filepath, project_root,
            failure="目录加载失败"))
        engines = ()
    for _label, _run in engines:
        try:
            channel_result = _run(code, tree, source_lines, filepath,
                                  exclude_rules)
        except Exception as _channel_exc:  # noqa: BLE001
            _log.warning("[Detectors] 引擎通道 %s 执行失败，已标记降级: %s",
                         _label, _channel_exc, exc_info=True)
            all_issues.append(_degraded_channel_issue(
                _label, _channel_exc, filepath, project_root))
            continue
        channel_items = _iter_detector_findings(channel_result)
        if channel_items is None:
            _log.warning(
                "[Detectors] 引擎通道 %s 返回契约外结果（%s），已标记降级",
                _label, type(channel_result).__name__)
            all_issues.append(_degraded_channel_issue(
                _label, TypeError("检测器必须返回可迭代的发现序列"),
                filepath, project_root))
            continue
        try:
            all_issues.extend(channel_items)
        except Exception as _channel_iter_exc:  # noqa: BLE001
            _log.warning(
                "[Detectors] 引擎通道 %s 结果迭代失败，保留已产出发现并标记降级: %s",
                _label, _channel_iter_exc, exc_info=True)
            all_issues.append(_degraded_channel_issue(
                _label, _channel_iter_exc, filepath, project_root))
    all_issues = filter_findings_with_context(all_issues, filepath)
    all_issues = apply_suppress_filter(all_issues, code)
    _result = deduplicate_issues(all_issues)
    if _use_cache and all(
            finding_rule_id(issue) != 'GATE-DEGRADED' for issue in _result):
        _store_cached_result(_cache_key, _result)
    return [dict(issue) for issue in _result]
def _early_channel_positional_arity(fn: Any) -> int:
    try:
        params = list(inspect.signature(fn).parameters.values())
    except (TypeError, ValueError):
        return 5
    if any(param.kind == param.VAR_POSITIONAL for param in params):
        return 5
    return sum(1 for param in params
               if param.kind in (param.POSITIONAL_ONLY,
                                 param.POSITIONAL_OR_KEYWORD))
def _invoke_early_channel(fn: Any, code: Any, tree: Any, source_lines: Any,
                          filepath: Any, exclude_rules: Any) -> Any:
    arity = _early_channel_positional_arity(fn)
    if arity == 3:
        return fn(tree, source_lines, filepath)
    if arity == 4:
        return fn(tree, source_lines, filepath, exclude_rules)
    return fn(code, tree, source_lines, filepath, exclude_rules)
def _phase_early_checks(all_issues: Any, code: Any, tree: Any, source_lines: Any,
                        filepath: Any, exclude_rules: Any = None,
                        skill_dir: Any = "") -> None:
    try:
        channels = early_channels()
    except Exception as _channels_exc:  # noqa: BLE001
        _log.warning("早期检查通道目录不可用，已标记降级: %s",
                     _channels_exc, exc_info=True)
        all_issues.append(_degraded_channel_issue(
            "early_catalog", _channels_exc, filepath, skill_dir,
            failure="目录加载失败"))
        return
    for _label, _run, _post_exclude in channels:
        _phase_start = len(all_issues)
        _raw = _run_channel_checked(
            _label,
            lambda _run=_run: _invoke_early_channel(
                _run, code, tree, source_lines, filepath, exclude_rules),
            filepath, skill_dir)
        _extend_detector_channel_issues(
            all_issues, _raw, _label, filepath, skill_dir)
        if _post_exclude:
            _drop_excluded_bridge_findings(all_issues, _phase_start,
                                           exclude_rules)
def _fn_rule_id(prefix: str, fn: Any) -> str:
    _m = _RULE_NUM_RE.search(fn.__name__)
    if not _m:
        return f"{prefix}-?"
    return f"{prefix}-{_m.group(1)}{_m.group(2).lower()}"
def _select_rule_fns(fns: list, prefix: str,
                     exclude_rules: Any) -> list:
    if not exclude_rules:
        return fns
    return [fn for fn in fns
            if not _is_excluded(_fn_rule_id(prefix, fn), exclude_rules)]
def _normalize_exclude_rules(exclude_rules: Any) -> frozenset[str] | None:
    if exclude_rules is None:
        return None
    normalized = normalize_id_set(exclude_rules)
    return frozenset(normalized) if normalized else None
def _is_excluded(rule_id: str, exclude_rules: Any) -> bool:
    return bool(exclude_rules) and bool(
        exclude_rules & normalize_id_set((rule_id,)))
def _filter_excluded_issues(issues: Any, exclude_rules: Any) -> Any:
    if not exclude_rules:
        return issues
    return [issue for issue in issues
            if not (isinstance(issue, dict)
                    and _is_excluded(str(issue.get("rule_id", "")),
                                     exclude_rules))]
def _drop_excluded_bridge_findings(all_issues: list, phase_start: int,
                                   exclude_rules: Any) -> None:
    all_issues[phase_start:] = _filter_excluded_issues(
        all_issues[phase_start:], exclude_rules)
def _phase_security_checks(all_issues: Any, tree: Any, source_lines: Any,
                           filepath: Any, exclude_rules: Any = None,
                           skill_dir: Any = "") -> None:
    if tree is None:
        _log.warning("安全检测阶段缺少 AST，跳过 SE/SL 规则族")
        return
    nodes = list(walk_nodes(tree))
    try:
        se_fns = _select_rule_fns(
            list(_sorted_catalog("se_checks").values()), "SE", exclude_rules)
    except KeyError as _se_exc:
        _log.warning("SE 检查规则目录不可用，已标记降级: %s", _se_exc)
        all_issues.append(_degraded_channel_issue(
            "SE_catalog", _se_exc, filepath, skill_dir,
            failure="目录加载失败"))
        se_fns = []
    try:
        sl_fns = _select_rule_fns(
            list(_sorted_catalog("sl_checks").values()), "SL", exclude_rules)
    except KeyError as _sl_exc:
        _log.warning("SL 检查规则目录不可用，已标记降级: %s", _sl_exc)
        all_issues.append(_degraded_channel_issue(
            "SL_catalog", _sl_exc, filepath, skill_dir,
            failure="目录加载失败"))
        sl_fns = []
    phase_start = len(all_issues)
    for fn in se_fns:
        raw = _run_channel_checked(
            getattr(fn, "__name__", "SE"),
            lambda fn=fn: fn(tree, source_lines, filepath, index=nodes),
            filepath, skill_dir)
        extend_issues(all_issues, raw, filepath, skill_dir=skill_dir)
    for fn in sl_fns:
        raw = _run_channel_checked(
            getattr(fn, "__name__", "SL"),
            lambda fn=fn: fn(tree, source_lines, filepath),
            filepath, skill_dir)
        extend_issues(all_issues, raw, filepath, skill_dir=skill_dir)
    _drop_excluded_bridge_findings(all_issues, phase_start, exclude_rules)
_RULE_NUM_RE = re.compile(r"(\d+)([A-Za-z]?)$")
def _release_gate_rule_state() -> None:
    global _GATE_RULE_CATALOG
    _GATE_RULE_CATALOG = None
    _gate_cache.clear()
    _scan_antipatterns_shared.cache_clear()
register_rebuild_hook("detect_result_cache", _DETECT_CACHE.clear)
register_rebuild_hook("project_context_cache", clear_project_context_cache)
register_rebuild_hook("gate_rule_state", _release_gate_rule_state)
_log.info("diag_detector_assembly 检测器装配侧已加载: %d 项导出", len(__all__))
def _include_ok(fp: str, include_file: Any) -> bool:
    if include_file is None:
        return True
    try:
        return bool(include_file(fp))
    except Exception as e:  # noqa: BLE001
        _log.warning(
            "[Detectors] include_file 谓词异常,跳过 %s: %s", fp, e)
        return False
def _walk_py_files(root_dir: str, include_file: Any = None) -> list:
    try:
        root = os.fsdecode(os.fspath(root_dir))
    except (TypeError, ValueError) as exc:
        raise TypeError(
            f"扫描根目录必须是 str/PathLike（{type(root_dir).__name__}）"
        ) from exc
    if not root or not os.path.isdir(root):
        raise ValueError(f"扫描根目录不存在或不是目录: {root_dir!r}")
    skip = scan_prune_dirs(root)
    py_files: list = []
    def _on_walk_error(exc: OSError) -> None:
        _log.warning("[Detectors] 目录遍历失败，跳过该子树: %s", exc)
    for dirpath, dirnames, filenames in os.walk(root, onerror=_on_walk_error):
        dirnames[:] = sorted(
            d for d in dirnames if not _is_pruned_scan_dirname(d, skip))
        for fname in sorted(filenames):
            if (not fname.lower().endswith('.py')
                    or fname.startswith('.')
                    or is_appledouble_basename(fname)):
                continue
            _fp = os.path.join(dirpath, fname)
            if _include_ok(_fp, include_file):
                py_files.append(_fp)
    return py_files
def _detector_scan_files(detector: Any, fpaths: list) -> list:
    findings: list = []
    label = _detector_label(detector)
    for fpath in fpaths:
        try:
            result = detector.detect_file(fpath)
        except Exception as e:
            _log.warning(
                "[Detectors] %s 检测失败 %s: %s", label, fpath, e,
                exc_info=True)
            raise RuntimeError(
                f"{label} 扫描 {fpath} 失败: {e}") from e
        items = _iter_detector_findings(result)
        if items is None:
            _log.warning(
                "[Detectors] %s 返回契约外结果（%s）: %s",
                label, type(result).__name__, fpath)
            raise TypeError(
                f"{label} 扫描 {fpath} 的结果必须可迭代，"
                f"实际为 {type(result).__name__}")
        try:
            findings.extend(items)
        except Exception as e:
            _log.warning(
                "[Detectors] %s 检测结果遍历中断 %s: %s",
                label, fpath, e, exc_info=True)
            raise RuntimeError(
                f"{label} 遍历 {fpath} 的检测结果失败: {e}") from e
    return findings
def _detector_label(detector: Any) -> str:
    if isinstance(detector, type):
        return getattr(detector, "DETECTOR_ID", detector.__name__)
    return getattr(detector, "DETECTOR_ID", type(detector).__name__)
def _construct_detector(detector_cls: type) -> Any:
    try:
        return detector_cls()
    except Exception as e:
        label = _detector_label(detector_cls)
        _log.warning(
            "[Detectors] %s 检测器构造失败: %s", label, e,
            exc_info=True)
        raise RuntimeError(f"{label} 检测器构造失败: {e}") from e
def _run_pattern_detector(detector_cls: type, py_files: list) -> list:
    detector = _construct_detector(detector_cls)
    if not hasattr(detector, 'detect_file'):
        label = _detector_label(detector_cls)
        _log.warning("[Detectors] %s 缺少 detect_file 方法", label)
        raise TypeError(f"{label} 缺少 detect_file 方法，无法执行扫描")
    return _detector_scan_files(detector, py_files)
def detect_all_new_patterns(
    root_dir: str,
    include_file: Any = None,
) -> list[PatternFinding]:
    py_files = _walk_py_files(root_dir, include_file)
    all_findings: list = []
    for detector_cls in _sorted_catalog("new_pattern_classes").values():
        all_findings.extend(_run_pattern_detector(detector_cls, py_files))
    return all_findings
def _count_by_detector(findings: list) -> dict[str, int]:
    summary: dict[str, int] = {}
    for f in findings:
        did = str(_finding_field(f, "detector_id", "UNKNOWN") or "UNKNOWN")
        summary[did] = summary.get(did, 0) + 1
    return summary
def quick_new_pattern_check(root_dir: str) -> dict[str, Any]:
    findings = detect_all_new_patterns(root_dir)
    return {
        "total_findings": len(findings),
        "by_detector": _count_by_detector(findings),
        "findings": findings,
    }
def detect_all_audit_patterns(
    root_dir: str,
    exclude_detectors: set[str] | frozenset | None = None,
    include_file: Callable[[str], bool] | None = None,
) -> list[PatternFinding]:
    _t0 = time.monotonic()
    py_files = _walk_py_files(root_dir, include_file)
    classes = dict(audit_registry_class_ids())
    excluded = normalize_id_set(exclude_detectors)
    run_ids = [did for did in classes if not _is_excluded(did, excluded)]
    all_findings: list[PatternFinding] = []
    for did in run_ids:
        all_findings.extend(_run_pattern_detector(classes[did], py_files))
    write_module_run(
        "diag_detector_assembly", "detect_all_audit_patterns",
        duration_ms=(time.monotonic() - _t0) * 1000.0,
        files=len(py_files), detectors=len(run_ids),
        findings=len(all_findings))
    return all_findings
def _is_test_py_path(path: str, root_dir: str) -> bool:
    try:
        rel = os.path.relpath(path, root_dir)
    except ValueError as exc:
        log_swallowed(__name__, exc,
                      context=f"_is_test_py_path:{type(exc).__name__}")
        rel = os.path.basename(path)
    return is_test_file_path(rel)
def quick_audit_pattern_check(root_dir: str, include_tests: bool = False) -> dict:
    include_tests = signal_bool(include_tests)
    include_file = None
    if not include_tests:
        include_file = lambda fp: not _is_test_py_path(fp, root_dir)
    findings = detect_all_audit_patterns(root_dir, include_file=include_file)
    summary = _count_by_detector(findings)
    write_module_run(
        "diag_detector_assembly", "quick_audit_pattern_check",
        findings=len(findings), total=len(summary))
    return {
        "total_findings": len(findings),
        "by_detector": summary,
        "findings": findings,
    }
SCORE_WEIGHTS = {
    "CRITICAL": SEVERITY_PENALTY_WEIGHTS["P0"],
    "HIGH": SEVERITY_PENALTY_WEIGHTS["P1"],
    "MEDIUM": SEVERITY_PENALTY_WEIGHTS["P2"],
    "LOW": SEVERITY_PENALTY_WEIGHTS["P3"],
    "P4": SEVERITY_PENALTY_WEIGHTS["P4"],
}
_SEVERITY_P_TO_WEIGHTED = {
    "P0": "CRITICAL", "P1": "HIGH", "P2": "MEDIUM", "P3": "LOW", "P4": "P4",
}
def _severity_score_bucket(raw: Any) -> str:
    text = severity_text_value(raw)
    if text is None:
        return "LOW"
    bucket = _SEVERITY_P_TO_WEIGHTED.get(text, text)
    if bucket in SCORE_WEIGHTS:
        return bucket
    if text in SEVERITY_RANK or re.match(r"^P\d+", text):
        return _SEVERITY_P_TO_WEIGHTED.get(normalize_severity(text), "LOW")
    return _SEVERITY_P_TO_WEIGHTED.get(diag_severity_to_p(text), "LOW")
@dataclass
class DiagnosisBaseline:
    score: float = 100.0
    crit_high: int = 0
    issues_total: int = 0
    by_severity: dict[str, int] = field(default_factory=dict)
    crit_high_rule_ids: set[str] = field(default_factory=set)
    def to_dict(self) -> dict[str, Any]:
        return {"score": round(self.score, 1), "crit_high": self.crit_high,
                "issues_total": self.issues_total,
                "by_severity": dict(self.by_severity),
                "crit_high_rule_ids": sorted(self.crit_high_rule_ids)}
def build_diag_baseline(code: str, filepath: str = "") -> DiagnosisBaseline:
    baseline = DiagnosisBaseline()
    raw_issues = detect_all(code, filepath)
    if not isinstance(raw_issues, list):
        raise TypeError(
            "detect_all 返回契约外结果 "
            f"{type(raw_issues).__name__}，无法建立可信诊断基线")
    if not raw_issues:
        return baseline
    for iss in raw_issues:
        _accumulate_issue(baseline, iss)
    penalty = sum(
        SCORE_WEIGHTS[sev] * cnt for sev, cnt in baseline.by_severity.items()
    )
    baseline.score = max(0.0, 100.0 - penalty)
    return baseline
def _accumulate_issue(baseline: DiagnosisBaseline, issue) -> None:
    if not isinstance(issue, dict):
        return
    sev = _severity_score_bucket(issue.get("severity"))
    baseline.by_severity[sev] = baseline.by_severity.get(sev, 0) + 1
    baseline.issues_total += 1
    if sev not in ("CRITICAL", "HIGH"):
        return
    baseline.crit_high += 1
    baseline.crit_high_rule_ids.add(rule_id_of(issue))
_DIAG_GUARD_EXC = ((AttributeError, KeyError, TypeError, RuntimeError, OSError)
                   + PARSE_DEGRADE_EXC)
DEFAULT_SCORE_DROP_TOLERANCE_PCT: float = 5.0
class DiagnosisRegressionGuard:
    def __init__(self,
                 score_drop_tolerance_pct: float = DEFAULT_SCORE_DROP_TOLERANCE_PCT) -> None:
        self.score_drop_tolerance_pct = coerce_tolerance(
            score_drop_tolerance_pct)
    def verify(
        self, original_code: str, fixed_code: str, filepath: str = "",
    ) -> dict[str, Any]:
        t0 = time.time()
        try:
            base = build_diag_baseline(original_code, filepath)
            after = build_diag_baseline(fixed_code, filepath)
        except _DIAG_GUARD_EXC as e:
            _log.warning("[DiagRegression] 诊断引擎异常，防御式放行: %s", e,
                           exc_info=True)
            return self._unverifiable_report(e, t0)
        reasons: list[str] = []
        crit_reason = _crit_high_regression_reason(base, after)
        if crit_reason:
            reasons.append(crit_reason)
            _log.warning(
                "[DiagRegression] 诊断回归: %s — 修复引入高危违规",
                "; ".join(reasons)[:200])
            return self._build_report("regressed", base, after, reasons, t0)
        score_reason = self._score_drop_reason(base, after)
        if score_reason:
            reasons.append(score_reason)
            _log.warning("[DiagRegression] 评分退化（非阻断）: %s",
                           "; ".join(reasons))
            return self._build_report("degraded", base, after, reasons, t0)
        if after.score > base.score or after.issues_total < base.issues_total:
            _log.info(
                "[DiagRegression] 诊断回归验证通过: score %.1f→%.1f, "
                "高危违规 %d→%d",
                base.score, after.score, base.crit_high, after.crit_high)
        return self._build_report("passed", base, after, reasons, t0)
    def _score_drop_reason(self, base: DiagnosisBaseline,
                           after: DiagnosisBaseline) -> str:
        score_drop_pct = (
            (base.score - after.score) / max(base.score, 1.0) * 100.0
        )
        if after.score < base.score and \
                score_drop_pct > self.score_drop_tolerance_pct:
            return (f"诊断评分下降: {base.score:.1f}→{after.score:.1f} "
                    f"({score_drop_pct:.1f}%)")
        return ""
    @staticmethod
    def _build_report(
        status: str, base: DiagnosisBaseline, after: DiagnosisBaseline,
        reasons: list[str], t0: float,
    ) -> dict[str, Any]:
        return {
            "status": status, "baseline": base.to_dict(), "after": after.to_dict(),
            "delta": {"score_delta": round(after.score - base.score, 1),
                      "crit_high_delta": after.crit_high - base.crit_high,
                      "issues_delta": after.issues_total - base.issues_total},
            "reasons": reasons, "elapsed_ms": round((time.time() - t0) * 1000, 1),
        }
    @staticmethod
    def _unverifiable_report(exc: Exception, t0: float) -> dict[str, Any]:
        return {
            "status": "unverifiable", "baseline": None, "after": None,
            "delta": {"score_delta": None, "crit_high_delta": None, "issues_delta": None},
            "reasons": [f"诊断引擎异常: {exc}"],
            "elapsed_ms": round((time.time() - t0) * 1000, 1),
        }
def _crit_high_regression_reason(base: DiagnosisBaseline,
                                 after: DiagnosisBaseline) -> str:
    crit_high_delta = after.crit_high - base.crit_high
    new_rules = sorted(after.crit_high_rule_ids - base.crit_high_rule_ids)
    if crit_high_delta <= 0 and not new_rules:
        return ""
    if crit_high_delta > 0:
        return (f"高危违规增多: {base.crit_high}→{after.crit_high}"
                + (f"（新增规则: {', '.join(new_rules[:5])}）"
                   if new_rules else ""))
    return (f"高危违规换血: {base.crit_high}→{after.crit_high}"
            f"（新增规则: {', '.join(new_rules[:5])}）")
def check_diag_regression(
    original_code: str, fixed_code: str, filepath: str = "",
    score_drop_tolerance_pct: float = DEFAULT_SCORE_DROP_TOLERANCE_PCT,
) -> dict[str, Any]:
    guard = DiagnosisRegressionGuard(score_drop_tolerance_pct=score_drop_tolerance_pct)
    return guard.verify(original_code, fixed_code, filepath=filepath)
_LOG_SUMMARY_MAX_CHARS = 150
def _log_defensive_pass(stage: str, exc: BaseException) -> None:
    _log.warning("[AIManualFix] %s异常(防御式放行): %s: %s",
                 stage, type(exc).__name__, exc, exc_info=exc)
def _diag_reasons_text(report: dict) -> str:
    reasons = report.get("reasons")
    if isinstance(reasons, str):
        return reasons
    if isinstance(reasons, (list, tuple)):
        return "; ".join(str(r) for r in reasons)
    return ""
def _diag_side_score(report: dict, side: str):
    part = report.get(side)
    score = part.get("score") if isinstance(part, dict) else None
    if isinstance(score, bool) or not isinstance(score, (int, float)):
        return None
    return score
def _diag_side_crit(report: dict, side: str):
    part = report.get(side)
    value = part.get("crit_high") if isinstance(part, dict) else None
    if isinstance(value, bool) or not isinstance(value, int):
        return None
    return value
def _diag_verdict(ctx: Any, report: dict) -> tuple[dict | None, bool]:
    status = report.get("status") if isinstance(report, dict) else None
    if status == "regressed":
        reason = _diag_reasons_text(report)[:200]
        _log.warning(
            "[AIManualFix] 诊断回归验证失败: %s — 拒绝写入（回滚语义）", reason)
        return aaf_reject(
            ctx, "rejected", f"诊断回归验证失败({reason}),已拒绝写入."
                             "修复引入新的高危诊断违规,需人工介入.",
            event="ai_fix_rejected",
            audit_reason=f"诊断回归退化: {reason}",
            diag_regression=report), False
    if status == "degraded":
        _log.warning(
            "[AIManualFix] 诊断评分退化(score %s→%s)，已降级标记交 AI 审核",
            _diag_side_score(report, "baseline"),
            _diag_side_score(report, "after"))
        return None, True
    if status == "unverifiable":
        _log.warning("[AIManualFix] 诊断回归验证未定论(%s)，防御式放行",
                       _diag_reasons_text(report)[:_LOG_SUMMARY_MAX_CHARS] or "引擎异常")
    elif status == "passed":
        _log.info(
            "[AIManualFix] 诊断回归验证通过: score %s→%s, 高危违规 %s→%s",
            _diag_side_score(report, "baseline"),
            _diag_side_score(report, "after"),
            _diag_side_crit(report, "baseline"),
            _diag_side_crit(report, "after"))
    else:
        _log.warning("[AIManualFix] 诊断回归验证返回契约外状态(%r)，防御式放行",
                       status)
    return None, False
def aaf_verify_diag(ctx: Any) -> tuple[dict | None, dict | None, bool]:
    diag_regression = None
    if ctx.fixed_source == ctx.original_source:
        return None, diag_regression, False
    try:
        report = DiagnosisRegressionGuard().verify(
            ctx.original_source, ctx.fixed_source, filepath=ctx.file_path)
        diag_regression = report
        reject, degraded = _diag_verdict(ctx, report)
    except Exception as e:  # noqa: BLE001
        log_swallowed(__name__, e,
                      context=f'aaf_verify_diag:{type(e).__name__}')
        _log_defensive_pass("诊断回归验证", e)
        return None, diag_regression, False
    return reject, diag_regression, degraded

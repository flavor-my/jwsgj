from __future__ import annotations

import ast
import copy
import hashlib
import json
import os
import re
import tempfile
import threading
import time
from collections import defaultdict
from collections.abc import Iterable
from dataclasses import dataclass, field
from typing import Any

from jwsgj import diag_testing_mutation_runtime as _runtime
from jwsgj.diag_detectors_registry import get_registry
from jwsgj.diag_guard_io import (
    check_path_traversal,
    read_source_text_strict,
)
from jwsgj.diag_solidify_rules import (
    AST_CHECKERS,
    RULES,
    delegated_sync_rule_ids,
)
from jwsgj.diag_testing_source import (
    FileCache,
    annotate_complexity_finding,
    annotate_safety_finding,
    build_mutation_test_mapping,
    file_content_digest,
    find_function_boundary,
)
from jwsgj.diag_types_defs import (
    TestMethodResult,
    dict_findings,
)
from jwsgj.diag_types_normalize import (
    finding_file_path,
    finite_float_or_zero,
    make_locator_fast,
    safe_finding_line,
    safe_int,
)
from jwsgj.diag_types_vocab import (
    MS_PER_SECOND,
    RULE_COMMAND_INJECTION,
    RULE_HARDCODED_SECRET,
    SEVERITY_RANK,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    SIGNAL_MUTATION_VERIFIED,
)
from jwsgj.fix_guide_rule_identity import (
    is_dead_code_finding,
    matches_rule_family,
)
from jwsgj.log_config import (
    get_module_logger,
    log_swallowed,
)
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.runtime_paths import (
    read_evolution_section,
    write_evolution_section,
)
from jwsgj.runtime_scope import (
    CACHE_TEMP_DIR_NAMES,
    GENERIC_SCAN_IGNORE_DIRS_LOWER,
    is_pruned_scan_dir,
    is_py_source_file,
    is_test_source_basename,
)

_log = get_module_logger(__name__)
__all__ = [
    'COMPLEXITY_RULE_KEYWORDS',
    'MAX_VERIFY_COUNT',
    'SAFETY_RULE_KEYWORDS',
    'MutationReport',
    'MutationResult',
    'MutationVerifier',
    'annotate_findings_with_mutation',
    'classify_finding_type',
    'collect_probe_template_candidates',
    'generate_mutants',
    'list_probe_template_candidates',
    'load_probe_templates',
    'register_probe_template',
    'run_cached_false_negative_probe',
    'run_false_negative_probe',
    'run_mutation_tests',
]
_log.info("diag_testing_mutation 判定层已加载：%d 项导出", len(__all__))
_GLOBAL_MUTATION_BUDGET = 60
_PER_FILE_MUTATION_BUDGET = 3
_PRESKIP_MUTATION_TYPES = frozenset({
    ast.Compare.__name__, ast.Return.__name__, ast.Constant.__name__,
})
_PRESKIP_ERROR = 'preskipped_low_confidence'
_DEFAULT_MAPPING_CONFIDENCE = 'low'
_MAX_MUTATION_FILE_FINDINGS = 20
def _preskip_low_confidence(all_mutants) -> tuple[list, list]:
    preskip_results = []
    eval_mutants = []
    for m in all_mutants:
        if (m.get('mapping_confidence') == _DEFAULT_MAPPING_CONFIDENCE
                and m.get('mutation_type') in _PRESKIP_MUTATION_TYPES):
            preskip_results.append({
                'rel_path': m['rel_path'],
                'line': m['line'],
                'killed': False,
                'error': _PRESKIP_ERROR,
            })
        else:
            eval_mutants.append(m)
    return preskip_results, eval_mutants
def _per_file_mutation_stats(eval_results) -> dict:
    per_file: dict = defaultdict(lambda: {'mutations': 0, 'killed': 0})
    for r in eval_results:
        stats = per_file[r['rel_path']]
        stats['mutations'] += 1
        if r['killed']:
            stats['killed'] += 1
    return dict(per_file)
def _per_file_score_findings(per_file) -> list:
    per_file_scores = []
    for fp, stats in per_file.items():
        file_score = (stats['killed'] / stats['mutations'] * 100) if stats['mutations'] > 0 else 0
        rounded_score = round(file_score, 1)
        per_file_scores.append({
            "file": fp,
            "mutations": stats['mutations'],
            "detected": stats['killed'],
            "survived": stats['mutations'] - stats['killed'],
            "score": rounded_score,
            "type": "mutation_file_score",
            "severity": "low",
            "message": f"突变分数 {rounded_score:.1f}% "
                       f"({stats['killed']}/{stats['mutations']})，"
                       f"预算受限采样，信号强度有限",
        })
    return sorted(per_file_scores, key=lambda x: x["score"])[:_MAX_MUTATION_FILE_FINDINGS]
def _cache_owner_matches(cache: object, skill_dir: str) -> bool:
    if not hasattr(cache, 'skill_dir'):
        return True
    owner = cache.skill_dir
    if not isinstance(owner, str) or not owner.strip():
        return False
    try:
        owner_root = os.path.realpath(os.path.abspath(owner))
        target_root = os.path.realpath(os.path.abspath(skill_dir))
    except (OSError, TypeError, ValueError):
        return False
    return os.path.normcase(owner_root) == os.path.normcase(target_root)


@dataclass(frozen=True, eq=False)
class _DefectTemplate:
    """单项缺陷注入模板。

    `sample_source` 是已知含缺陷的最小源码，`clean_source` 是无缺陷
    对照；两者必须成对：只测 sample 会激活“能报但不准”的规则，反而
    拉低诊断精度，因此 clean 误报直接否决激活。

    `sample_files`/`clean_files` 用于真跨文件规则（如 CS-106 靠
    `os.path.dirname(filepath)` 读同目录兄弟模块）：非空时探针会在
    临时目录还原多文件布局并逐文件判定，`sample_source` 不再使用。
    `primary_file` 指定交给 DetectorRegistry 验证的主文件（默认第一个）。
    """
    template_id: str
    rule_id: str
    rule_family: str
    severity: str
    sample_source: str
    clean_source: str
    requires_context: bool = False
    sample_files: dict[str, str] = field(default_factory=dict)
    clean_files: dict[str, str] = field(default_factory=dict)
    primary_file: str = ''
_DEFECT_TEMPLATES: tuple[_DefectTemplate, ...] = (
    _DefectTemplate(
        'bare_except', 'CS-01', 'exception_handling', 'P1',
        'def f():\n    try:\n        return 1\n    except:\n        return 0\n',
        'def f():\n    try:\n        return 1\n    except ValueError:\n        return 0\n'),
    _DefectTemplate(
        'mutable_default', 'CS-04', 'api_contract', 'P1',
        'def f(x=[]):\n    x.append(1)\n    return x\n',
        'def f(x=None):\n    return x\n'),
    _DefectTemplate(
        'silent_except_pass', 'CS-05', 'exception_handling', 'P1',
        'def f():\n    try:\n        return 1\n    except:\n        pass\n',
        'def f():\n    try:\n        return 1\n    except Exception:\n        raise\n'),
    _DefectTemplate(
        'subprocess_shell', 'CS-17', 'security', 'P1',
        'import subprocess\ndef f(c):\n    subprocess.run(c, shell=True)\n',
        'import subprocess\ndef f(c):\n    subprocess.run([c], shell=False)\n'),
    _DefectTemplate(
        'eval_exec', 'CS-18', 'security', 'P1',
        'def f(x):\n    return eval(x)\n',
        'import ast\ndef f(x):\n    return ast.literal_eval(x)\n'),
    _DefectTemplate(
        'pickle_load', 'CS-20', 'security', 'P1',
        'import pickle\ndef f(b):\n    return pickle.loads(b)\n',
        'import json\ndef f(b):\n    return json.loads(b)\n'),
    _DefectTemplate(
        'requests_verify', 'CS-21', 'security', 'P1',
        'import requests\ndef f(u):\n    return requests.get(u, verify=False)\n',
        'import requests\ndef f(u):\n    return requests.get(u, verify=True)\n'),
    _DefectTemplate(
        'assert_in_prod', 'CS-23', 'error_handling', 'P2',
        'def f(x):\n    assert x > 0\n    return x\n',
        'def f(x):\n    if x <= 0:\n        raise ValueError(x)\n    return x\n'),
    _DefectTemplate(
        'yaml_load', 'CS-24', 'security', 'P1',
        'import yaml\ndef f(s):\n    return yaml.load(s)\n',
        'import yaml\ndef f(s):\n    return yaml.safe_load(s)\n'),
    _DefectTemplate(
        # 缺陷样本必须真的引用异常对象（``str(e)`` 而未绑定 → NameError）。
        # 只写 ``except ValueError: return 0`` 并不需要异常对象，补 ``as e``
        # 反而制造未使用变量（F841）——拿它当缺陷样本等于用假前提校验规则。
        'except_missing_as', 'CS-61', 'exception_handling', 'P2',
        'def f():\n    try:\n        return 1\n    except ValueError:\n        return str(e)\n',
        'def f():\n    try:\n        return 1\n    except ValueError as e:\n        return str(e)\n'),
    _DefectTemplate(
        'decorator_no_wraps', 'CS-64', 'api_contract', 'P2',
        ('def deco(fn):\n    def wrap(*a, **k):\n        return fn(*a, **k)\n'
         '    return wrap\n'),
        ('import functools\ndef deco(fn):\n    @functools.wraps(fn)\n'
         '    def wrap(*a, **k):\n        return fn(*a, **k)\n    return wrap\n')),
    _DefectTemplate(
        'format_injection', 'CS-76', 'security', 'P2',
        'def f(tpl, v):\n    return tpl.format(v)\n',
        'def f(tpl, v):\n    return tpl.replace("{}", str(v))\n'),
    _DefectTemplate(
        'except_pass_governance', 'CS-89', 'exception_handling', 'P2',
        ('def f():\n    try:\n        return 1\n    except ValueError:\n'
         '        pass\n'),
        ('def f():\n    try:\n        return 1\n    except ValueError as e:\n'
         '        log.warning("%s", e)\n')),
    _DefectTemplate(
        'inline_exemption_contains', 'CS-99', 'test_hygiene', 'P2',
        'def f(line):\n    return "noqa" in line\n',
        ('def f(line):\n    _cut = line.find("#")\n'
         '    return "noqa" in line[:_cut]\n')),
    _DefectTemplate(
        'split_line_count', 'CS-100', 'line_counting', 'P2',
        ('def count_lines(source):\n'
         '    return len(source.split("\\n"))\n'),
        ('def count_lines(source):\n'
         '    return source.count("\\n") + 1\n')),
    _DefectTemplate(
        'namespace_cartesian_shortfall', 'CS-101', 'project_convention', 'P2',
        ('ATTRS = ["a", "b"]\nNS = ["x", "y"]\n'
         'TABLE = {"x.a": 1, "x.b": 2}\n'),
        ('ATTRS = ["a", "b"]\nNS = ["x", "y"]\n'
         'TABLE = {"x.a": 1, "x.b": 2, "y.a": 3, "y.b": 4}\n')),
    _DefectTemplate(
        'local_compact_timestamp', 'CS-102', 'time_format', 'P2',
        ('import time\n\ndef stamp():\n'
         '    base = time.strftime("%Y%m%d%H%M%S")\n'
         '    return f"{base}{int(time.time() * 1000) % 1000:03d}"\n'),
        ('def stamp():\n    return format_compact_ts()\n')),
    _DefectTemplate(
        'missing_file_logged', 'CS-103', 'exception_handling', 'P2',
        ('import json\n\ndef load(path):\n    try:\n'
         '        with open(path) as handle:\n'
         '            return json.load(handle)\n'
         '    except FileNotFoundError:\n'
         '        log_swallowed(__name__, "missing", path)\n'
         '        return None\n'),
        ('import json\nimport os\n\ndef load(path):\n'
         '    if not os.path.isfile(path):\n        return None\n'
         '    with open(path) as handle:\n'
         '        return json.load(handle)\n')),
    _DefectTemplate(
        'derived_rule_id_literal_copy', 'CS-104', 'ssot_hygiene', 'P2',
        ('RULES = {"first": "CS-01", "second": "CS-01"}\n'
         'ORDER = ["CS-01", "CS-01"]\n'),
        ('RULES = {"first": "CS-01", "second": "CS-02"}\n'
         'ORDER = ["CS-01", "CS-02"]\n')),
    _DefectTemplate(
        'dual_projection_drift', 'CS-105', 'ssot_hygiene', 'P2',
        ('def _src():\n    return {}\n\ndef delegate():\n    return _src()\n'
         '\ndef handrolled():\n    a = _src()\n'
         '    return {"k": a.get("x"), "j": a.get("y")}\n'),
        ('def _src():\n    return {}\n\ndef delegate():\n    return _src()\n'
         '\ndef handrolled():\n    a = {}\n'
         '    return {"k": a.get("x"), "j": a.get("y")}\n')),
    _DefectTemplate(
        'private_entry_contract_split', 'CS-106', 'api_contract', 'P2',
        '', '',
        sample_files={
            'helper.py': 'def fetch():\n    return {}\n',
            'consumer.py': (
                'from . import helper\n\ndef _fetch():\n    return None\n'),
        },
        clean_files={
            'helper.py': 'def fetch():\n    return {}\n',
            'consumer.py': (
                'from . import helper\n\ndef _fetch():\n    return {}\n'),
        },
        primary_file='consumer.py'),
    _DefectTemplate(
        'unordered_finding_truncation', 'FD-01', 'finding_pruning', 'P1',
        ('def trim(findings, severity):\n'
         '    findings = findings[:5]\n'
         '    return findings, severity\n'),
        'def trim(findings, severity):\n    return findings, severity\n'),
    _DefectTemplate(
        'local_complexity_branch_table', 'FD-02', 'complexity_ssot', 'P2',
        ('from shared import cyclomatic_complexity\n\ndef score(node):\n'
         '    hits = 0\n'
         '    if isinstance(node, (If, For)):\n        hits += 1\n'
         '    return hits\n'),
        ('from shared import cyclomatic_complexity\n\ndef score(node):\n'
         '    return cyclomatic_complexity(node)\n')),
    _DefectTemplate(
        'decorator_blind_line_span', 'FD-03', 'span_ssot', 'P2',
        ('def span(node):\n'
         '    node = isinstance(node, (FunctionDef, ClassDef))\n'
         '    return 0 < node[0] < node.end_lineno\n'),
        ('def span(node):\n'
         '    node = isinstance(node, (FunctionDef, ClassDef))\n'
         '    return own_scope_line_span(node)\n')),
    _DefectTemplate(
        'main_guard_live_branch_copy', 'FD-04', 'main_guard_ssot', 'P2',
        ('def f(node):\n    if main_guard_branch(node):\n'
         '        return node.body + node.orelse\n'),
        'def f(node):\n    return main_guard_live_body(node)\n'),
    _DefectTemplate(
        'named_arg_without_kwonly', 'FD-05', 'api_contract', 'P2',
        ('def check(keyword, spec):\n    params = spec.args\n'
         '    if keyword.arg in params:\n        return True\n'),
        ('def check(keyword, spec):\n    params = spec.args\n'
         '    options = spec.kwonlyargs\n'
         '    if keyword.arg in params or keyword.arg in options:\n'
         '        return True\n')),
)
_PROBE_METHOD_ID = 'false_negative_probe'
_PROBE_METHOD_NAME = '漏报注入探针'
_PROBE_FN_RATE_LIMIT = 0.2
_PROBE_CANDIDATE_LIMIT = 20
_PROBE_TEMPLATE_ACTIVE_LIMIT = 30
_PROBE_EXCERPT_CONTEXT = 8
_HIST_TEMPLATE_PREFIX = 'hist_'
_REPAIRED_STATUSES = frozenset({'fixed', 'ai_fixed', 'succeeded'})

def _code_excerpt(source: str, line: int,
                  context: int = _PROBE_EXCERPT_CONTEXT) -> str:
    lines = source.splitlines()
    if not lines:
        return ''
    line = max(1, min(safe_int(line) or 1, len(lines)))
    start = max(0, line - 1 - context)
    end = min(len(lines), line + context)
    return '\n'.join(lines[start:end])

def _read_text_safe(path: str) -> str:
    if not path:
        return ''
    try:
        with open(path, encoding='utf-8-sig', errors='replace') as handle:
            return handle.read()
    except OSError:
        return ''

def _candidate_id(rule_id: str, anchor: str) -> str:
    digest = hashlib.sha1(
        f'{rule_id}:{anchor}'.encode(),
        usedforsecurity=False).hexdigest()[:10]
    return f'{_HIST_TEMPLATE_PREFIX}{rule_id}_{digest}'

def list_probe_template_candidates(skill_dir: str) -> dict:
    """读取待 AI 审核的历史缺陷模板候选（只读，不激活）。"""
    if not skill_dir:
        return {'candidates': [], 'total': 0}
    try:
        document = read_evolution_section(
            skill_dir, 'probe_template_candidates', {})
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 候选清单读取失败: %s', exc)
        return {'candidates': [], 'total': 0}
    entries = (document.get('candidates')
               if isinstance(document, dict) else None)
    if not isinstance(entries, list):
        return {'candidates': [], 'total': 0}
    pending = [item for item in entries
               if isinstance(item, dict)
               and item.get('status') == 'pending_review']
    return {'candidates': pending, 'total': len(pending)}

def collect_probe_template_candidates(
        skill_dir: str, *, limit: int = _PROBE_CANDIDATE_LIMIT) -> dict:
    """从已真实修复的历史 finding 生成探针模板候选（不自动激活）。

    只有 `fixed/ai_fixed/succeeded` 才有“修复前/后”对照价值：
    `sample_source` 取修复前（备份文件片段），`clean_source` 取修复后
    （当前文件片段）。无备份的条目只留代码摘录并标记 `needs_manual_sample`，
    由 AI 审核时补写最小样例。

    本函数只写候选清单；激活必须显式调用 `register_probe_template`——
    自动生成不等于自动激活，真实缺陷样例需要 AI 判定后才进入探针。
    """
    empty = {'candidates': [], 'total': 0, 'needs_manual': 0, 'stored': 0}
    if not skill_dir:
        return {**empty, 'error': 'skill_dir 为空'}
    try:
        from jwsgj.runtime_paths import (
            read_evolution_section,
            write_evolution_section,
        )
        from jwsgj.treatment_state import load_treatment_items
    except ImportError as exc:
        _log.warning('[FN_Probe] 候选采集依赖不可用: %s', exc)
        return {**empty, 'error': f'依赖不可用: {exc}'}
    try:
        items = load_treatment_items(skill_dir)
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 治疗台账读取失败: %s', exc)
        return {**empty, 'error': f'治疗台账不可读: {exc}'}
    existing = read_evolution_section(
        skill_dir, 'probe_template_candidates', {})
    known = {
        str(item.get('candidate_id')) for item in
        (existing.get('candidates') if isinstance(existing, dict) else None) or []
        if isinstance(item, dict)
    }
    active_doc = read_evolution_section(skill_dir, 'probe_templates', {})
    active = {
        str(item.get('candidate_id')) for item in
        (active_doc.get('templates') if isinstance(active_doc, dict) else None) or []
        if isinstance(item, dict)
    }
    seen = known | active
    fresh: list[dict] = []
    for item in items:
        if len(fresh) >= limit:
            break
        if not isinstance(item, dict):
            continue
        status = str(item.get('status') or '').strip().lower()
        if status not in _REPAIRED_STATUSES:
            continue
        rule_id = str(item.get('rule_id') or '').strip()
        if not rule_id:
            continue
        file_path = str(item.get('file_path') or item.get('file') or '')
        line = safe_int(item.get('line')) or 0
        backup = str(item.get('backup') or item.get('backup_path') or '')
        original = _read_text_safe(backup)
        current = _read_text_safe(file_path)
        sample = _code_excerpt(original, line) if original else ''
        clean = _code_excerpt(current, line) if current else ''
        candidate_id = _candidate_id(
            rule_id, sample or f'{file_path}:{line}')
        if candidate_id in seen:
            continue
        seen.add(candidate_id)
        fresh.append({
            'candidate_id': candidate_id,
            'rule_id': rule_id,
            'rule_family': str(
                item.get('domain') or item.get('rule_family') or 'unknown'),
            'severity': str(item.get('severity') or 'P2'),
            'file': file_path,
            'line': line,
            'description': str(item.get('description') or '')[:200],
            'sample_source': sample,
            'clean_source': clean,
            'source_status': status,
            'needs_manual_sample': not bool(sample.strip()),
            'status': 'pending_review',
        })
    merged = list((existing.get('candidates')
                   if isinstance(existing, dict) else None) or []) + fresh
    payload = {
        'generated_at': time.strftime('%Y-%m-%d %H:%M:%S'),
        'candidates': merged[-limit * 3:],
        'total': len(merged),
    }
    try:
        write_evolution_section(
            skill_dir, 'probe_template_candidates', payload)
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 候选落盘失败: %s', exc)
        return {**empty, 'candidates': fresh,
                'total': len(fresh), 'error': f'候选落盘失败: {exc}'}
    return {
        'candidates': fresh,
        'total': len(fresh),
        'needs_manual': sum(1 for item in fresh
                            if item['needs_manual_sample']),
        'stored': len(payload['candidates']),
    }

def register_probe_template(
        skill_dir: str, candidate_id: str, *,
        sample_source: str | None = None,
        clean_source: str | None = None,
        reviewer: str = 'ai', note: str = '') -> dict:
    """AI 审核通过后激活一条历史缺陷模板。

    校验：候选存在、`rule_id` 已固化、`sample_source` 可 AST 解析。
    `clean_source` 为空时退化为只测召回（该规则在无缺陷样本上的误报
    无法被否决），建议补齐。只接受 AI 审核后的显式调用，探针不会
    自行激活候选。
    """
    if not skill_dir or not candidate_id:
        return {'registered': False, 'error': 'skill_dir/candidate_id 为空'}
    try:
        from jwsgj.runtime_paths import (
            read_evolution_section,
            write_evolution_section,
        )
    except ImportError as exc:
        return {'registered': False, 'error': f'依赖不可用: {exc}'}
    document = read_evolution_section(
        skill_dir, 'probe_template_candidates', {})
    entries = (document.get('candidates')
               if isinstance(document, dict) else None) or []
    candidate = next((item for item in entries
                      if isinstance(item, dict)
                      and item.get('candidate_id') == candidate_id), None)
    if candidate is None:
        return {'registered': False, 'error': 'candidate_not_found'}
    rule_id = str(candidate.get('rule_id') or '').strip()
    try:
        from jwsgj.diag_solidify_rules import RULES
        solidified = {rule.rule_id for rule in RULES}
    except ImportError as exc:
        return {'registered': False, 'error': f'规则库不可用: {exc}'}
    if rule_id not in solidified:
        return {'registered': False,
                'error': f'rule_not_solidified: {rule_id}'}
    sample = (sample_source if sample_source is not None
              else candidate.get('sample_source')) or ''
    clean = (clean_source if clean_source is not None
             else candidate.get('clean_source')) or ''
    sample = str(sample)
    clean = str(clean)
    if not sample.strip():
        return {'registered': False, 'error': 'sample_source_empty'}
    try:
        ast.parse(sample)
    except SyntaxError as exc:
        return {'registered': False,
                'error': f'sample_source_unparsable: {exc}'}
    active_doc = read_evolution_section(skill_dir, 'probe_templates', {})
    templates = [item for item in
                 ((active_doc.get('templates')
                   if isinstance(active_doc, dict) else None) or [])
                 if isinstance(item, dict)
                 and item.get('template_id') != candidate_id]
    templates.append({
        'template_id': candidate_id,
        'candidate_id': candidate_id,
        'rule_id': rule_id,
        'rule_family': str(candidate.get('rule_family') or 'unknown'),
        'severity': str(candidate.get('severity') or 'P2'),
        'sample_source': sample,
        'clean_source': clean,
        'active': True,
        'approved_by': str(reviewer or 'ai'),
        'approved_at': time.strftime('%Y-%m-%d %H:%M:%S'),
        'note': str(note or '')[:300],
    })
    templates = templates[-_PROBE_TEMPLATE_ACTIVE_LIMIT:]
    try:
        write_evolution_section(
            skill_dir, 'probe_templates',
            {'templates': templates, 'total': len(templates)})
    except (OSError, ValueError, TypeError) as exc:
        return {'registered': False, 'error': f'模板落盘失败: {exc}'}
    approved_at = time.strftime('%Y-%m-%d %H:%M:%S')
    updated: list[dict] = []
    for item in entries:
        if not isinstance(item, dict):
            continue
        if item.get('candidate_id') == candidate_id:
            item = {
                **item,
                'status': 'approved',
                'approved_by': str(reviewer or 'ai'),
                'approved_at': approved_at,
                'activated_template_id': candidate_id,
            }
        updated.append(item)
    try:
        write_evolution_section(
            skill_dir, 'probe_template_candidates',
            {**document, 'candidates': updated})
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 候选状态回写失败（模板已激活）: %s', exc)
    return {
        'registered': True,
        'template_id': candidate_id,
        'rule_id': rule_id,
        'active_total': len(templates),
    }

def load_probe_templates(skill_dir: str) -> list[_DefectTemplate]:
    """读取 AI 已审核激活的历史缺陷模板（只读 active）。"""
    if not skill_dir:
        return []
    try:
        document = read_evolution_section(skill_dir, 'probe_templates', {})
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 模板加载失败: %s', exc)
        return []
    entries = (document.get('templates')
               if isinstance(document, dict) else None)
    if not isinstance(entries, list):
        return []
    templates: list[_DefectTemplate] = []
    for entry in entries:
        if not isinstance(entry, dict) or not entry.get('active'):
            continue
        sample = str(entry.get('sample_source') or '')
        if not sample.strip():
            continue
        templates.append(_DefectTemplate(
            template_id=str(entry.get('template_id') or 'hist_unknown'),
            rule_id=str(entry.get('rule_id') or ''),
            rule_family=str(entry.get('rule_family') or 'unknown'),
            severity=str(entry.get('severity') or 'P2'),
            sample_source=sample,
            clean_source=str(entry.get('clean_source') or ''),
        ))
    return templates

def _all_probe_templates(skill_dir: str) -> tuple:
    try:
        extra = tuple(load_probe_templates(skill_dir))
    except (OSError, ValueError, TypeError) as exc:
        _log.warning('[FN_Probe] 历史模板加载失败（仅用内置模板）: %s', exc)
        extra = ()
    return _DEFECT_TEMPLATES + extra
def _probe_authority_ready() -> int:
    """将 AST_CHECKERS 的权威 checker 挂到检测器注册表。

    DetectorRegistry 默认不持有这些 checker：26 条固化规则全部
    `is_registered == False`。未挂载时 register_solidified_rule 只能
    退化为 5 条启发式匹配，22 条规则恒不触发——这正是漏报的根因。
    这里显式装载，返回装载条数。
    """
    rule_map = {rule.rule_id: rule for rule in RULES}
    authority = {
        rid: (checker, rule_map[rid])
        for rid, checker in AST_CHECKERS.items()
        if rid in rule_map and rule_map[rid].enabled}
    return get_registry().install_solidified_authority(authority)
def _probe_record(tpl: _DefectTemplate, verdict: str,
                  detail: str = '') -> dict:
    return {
        'template_id': tpl.template_id,
        'rule_id': tpl.rule_id,
        'rule_family': tpl.rule_family,
        'severity': tpl.severity,
        'verdict': verdict,
        'detail': detail,
    }
_PROBE_DELEGATED = 'delegated_to_other_subsystem'
def _checker_hits(checker, rule, source: str, filepath: str = '<fn_probe>') -> bool:
    findings: list = []
    checker(ast.parse(source), rule, findings, filepath)
    return bool(findings)
def _materialize_files(root: str, name: str,
                       files: dict[str, str]) -> str:
    """把多文件样本还原到临时目录，返回样本根目录。"""
    base = os.path.join(root, name)
    for rel, content in files.items():
        path = os.path.join(base, rel.replace('/', os.sep))
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(path, 'w', encoding='utf-8') as handle:
            handle.write(content)
    return base
def _files_hit(checker, rule, base: str, files: dict[str, str]) -> bool:
    """在已还原的目录上逐文件跑 checker，任一命中即算检出。"""
    for rel in files:
        path = os.path.join(base, rel.replace('/', os.sep))
        with open(path, encoding='utf-8') as handle:
            tree = ast.parse(handle.read())
        findings: list = []
        checker(tree, rule, findings, path)
        if findings:
            return True
    return False
def _probe_multi_file(tpl: _DefectTemplate, checker, rule) -> dict:
    """多文件模板探针：还原同级模块布局后逐文件判定。

    CS-106 这类规则靠 `os.path.dirname(filepath)` 读同目录兄弟模块，
    没有真实文件系统就无法判定。临时目录即用即删，不污染技能根；
    主文件仍交给 DetectorRegistry 跑一遍，保证“接线”维度同样受验。
    """
    registry = get_registry()
    try:
        with tempfile.TemporaryDirectory(prefix='fnprobe_') as root:
            sample_dir = _materialize_files(root, 'sample', tpl.sample_files)
            if not _files_hit(checker, rule, sample_dir, tpl.sample_files):
                return _probe_record(tpl, 'survived', 'checker_missed')
            clean_dir = _materialize_files(root, 'clean', tpl.clean_files)
            if _files_hit(checker, rule, clean_dir, tpl.clean_files):
                return _probe_record(
                    tpl, 'false_alarm', 'checker_overreports')
            primary = tpl.primary_file or next(iter(tpl.sample_files))
            if not _ensure_wired(registry, tpl):
                return _probe_record(tpl, 'survived', 'wiring_failed')
            wired = registry.run(
                tpl.rule_id,
                source_code=tpl.sample_files[primary],
                file_path=os.path.join(
                    sample_dir, primary.replace('/', os.sep)))
            if not dict_findings(wired):
                return _probe_record(tpl, 'survived', 'wired_but_no_finding')
    except Exception as exc:  # noqa: BLE001 — 单模板异常不阻断整轮探针
        log_swallowed(
            __name__, exc, context=f'_probe_multi_file:{tpl.rule_id}')
        return _probe_record(tpl, 'error', type(exc).__name__)
    record = _probe_record(tpl, 'killed', 'activated')
    record['activation'] = 'activated'
    return record
def _solidify_symbols() -> tuple:
    return AST_CHECKERS, RULES, delegated_sync_rule_ids()
def _ensure_wired(registry, tpl: _DefectTemplate) -> bool:
    """确保模板规则已进入检测器注册表（含权威兜底）。

    DetectorRegistry.unregister 会一并清除 `_solidified_authority`，
    注销后 register_solidified_rule 拿不到权威，只能退化为 5 条启发式
    匹配而失效。这里在注册前重装权威，否则探针的“激活”动作会被注销
    副作用静默打断（表现为 wired_but_no_finding）。
    """
    if registry.is_registered(tpl.rule_id):
        return True
    _probe_authority_ready()
    registry.register_solidified_rule(
        rule_id=tpl.rule_id, pattern_type='ast', pattern='',
        severity=tpl.severity)
    return registry.is_registered(tpl.rule_id)
def _probe_one(tpl: _DefectTemplate) -> dict:
    """单个模板的注入探针，分“能力”与“接线”两个维度判定。

    能力：checker 能否从样本中得到 finding（并用无缺陷对照否决误报）。
    接线：该 rule_id 是否已进入 DetectorRegistry（管线实际会跑）。
    两者缺一即为漏报——有能力但未接线，诊断依旧静默漏过。
    """
    if tpl.requires_context:
        return _probe_record(tpl, 'skipped', 'requires_context')
    try:
        checkers, rules, delegated_ids = _solidify_symbols()
        checker = checkers.get(tpl.rule_id)
        if checker is None:
            return _probe_record(tpl, 'survived', 'no_checker')
        rule = next((r for r in rules if r.rule_id == tpl.rule_id), None)
        if rule is None:
            return _probe_record(tpl, 'survived', 'no_rule_spec')
        if tpl.sample_files:
            return _probe_multi_file(tpl, checker, rule)
        if not _checker_hits(checker, rule, tpl.sample_source):
            return _probe_record(tpl, 'survived', 'checker_missed')
        if _checker_hits(checker, rule, tpl.clean_source):
            return _probe_record(tpl, 'false_alarm', 'checker_overreports')
    except Exception as exc:  # noqa: BLE001 — 单模板异常不阻断整轮探针
        log_swallowed(
            __name__, exc, context=f'_probe_one:{tpl.rule_id}')
        return _probe_record(tpl, 'error', type(exc).__name__)
    if tpl.rule_id in delegated_ids:
        return _probe_record(tpl, 'killed', _PROBE_DELEGATED)
    registry = get_registry()
    try:
        if not _ensure_wired(registry, tpl):
            return _probe_record(tpl, 'survived', 'wiring_failed')
        wired = dict_findings(registry.run(
            tpl.rule_id, source_code=tpl.sample_source,
            file_path='<fn_probe>'))
    except Exception as exc:  # noqa: BLE001 — 接线失败计为漏报
        log_swallowed(
            __name__, exc, context=f'_probe_one:wiring:{tpl.rule_id}')
        return _probe_record(tpl, 'survived', 'wiring_failed')
    if not wired:
        return _probe_record(tpl, 'survived', 'wired_but_no_finding')
    record = _probe_record(tpl, 'killed', 'activated')
    record['activation'] = 'activated'
    return record
def _probe_finding(outcome: dict) -> dict:
    survived = outcome['verdict'] == 'survived'
    return {
        'type': 'false_negative' if survived else 'probe_false_alarm',
        'rule_id': outcome['rule_id'],
        'severity': 'P1' if survived else 'P2',
        'file': '<fn_probe>',
        'line': 0,
        'template_id': outcome['template_id'],
        'rule_family': outcome['rule_family'],
        'verdict': outcome['verdict'],
        'probe_detail': outcome['detail'],
        'message': (
            f"漏报探针：模板 {outcome['template_id']} 注入后未被 "
            f"{outcome['rule_id']} 检出"
            if survived else
            f"漏报探针：{outcome['rule_id']} 在无缺陷对照样本上误报，"
            f"拒绝激活"),
    }
_FN_BACKLOG_REASONS = {
    'no_checker': 'missing_checker',
    'no_rule_spec': 'missing_rule_spec',
    'checker_missed': 'checker_logic_gap',
    'wiring_failed': 'wiring_regression',
    'wired_but_no_finding': 'wiring_regression',
    'checker_overreports': 'precision_violation',
}
def _probe_backlog(outcomes: list[dict]) -> list[dict]:
    """把探针失败项归因成可执行的待补清单。

    原计划是“族内已有检测器 → 提升证据权重”，但 evidence_weights
    是方法级（`_EVIDENCE_WEIGHT_DB` 以 method 为 key），没有规则族
    维度；探针又是规则级（CS-61 等），两者无法对齐。而
    `cv_confidence_thresholds` 虽是规则级，却作用于“已产出 finding
    的确认”，对“根本不报”的漏报无效。

    与其伪造一个没有消费者的权重项，不如输出带归因的 backlog：
    缺 checker / checker 逻辑缺口 / 接线回退 / 精确度越界，
    每类对应不同的修复动作。
    """
    backlog: list[dict] = []
    for outcome in outcomes:
        if outcome['verdict'] not in ('survived', 'false_alarm'):
            continue
        reason = _FN_BACKLOG_REASONS.get(
            outcome['detail'], 'unclassified')
        backlog.append({
            'template_id': outcome['template_id'],
            'rule_id': outcome['rule_id'],
            'rule_family': outcome['rule_family'],
            'severity': outcome['severity'],
            'reason': reason,
            'detail': outcome['detail'],
        })
    return backlog
def _persist_probe_activations(skill_dir: str,
                               outcomes: list[dict]) -> int:
    """落盘漏报探针基线，供门禁与趋势判定使用。

    激活本身是进程内的幂等动作（`_probe_one` 内完成）；不在这里写
    固化 SSOT——SSOT 由 stage6d 独占，两处写同一文件会互相覆盖。
    只保留最近若干轮，避免无界增长。
    """
    activated = [
        o['rule_id'] for o in outcomes
        if o['verdict'] == 'killed' and o.get('activation') == 'activated']
    survived = [o['rule_id'] for o in outcomes if o['verdict'] == 'survived']
    has_evidence = any(
        o['verdict'] in ('killed', 'survived', 'false_alarm')
        for o in outcomes)
    if not skill_dir or not has_evidence:
        return len(activated)
    try:
        history = read_evolution_section(skill_dir, 'fn_probe_history')
        rounds = history.get('rounds') if isinstance(history, dict) else None
        rounds = list(rounds) if isinstance(rounds, list) else []
        rounds.append({
            'ts': time.strftime('%Y-%m-%d %H:%M:%S'),
            'templates': len(outcomes),
            'killed': len([
                o for o in outcomes if o['verdict'] == 'killed']),
            'activated': sorted(activated),
            'survived': sorted(survived),
            'pending': _probe_backlog(outcomes),
        })
        write_evolution_section(
            skill_dir, 'fn_probe_history', {'rounds': rounds[-20:]})
    except (OSError, ValueError, TypeError) as exc:
        log_swallowed(
            __name__, exc, context='_persist_probe_activations')
    return len(activated)
def _apply_probe_outcome(result: TestMethodResult, outcomes: list[dict],
                         activated: int) -> None:
    killed = [o for o in outcomes if o['verdict'] == 'killed']
    survived = [o for o in outcomes if o['verdict'] == 'survived']
    false_alarm = [o for o in outcomes if o['verdict'] == 'false_alarm']
    skipped = [
        o for o in outcomes if o['verdict'] in ('skipped', 'error')]
    evaluated = len(killed) + len(survived)
    fn_rate = (len(survived) / evaluated) if evaluated else 0.0
    total = len(outcomes)
    result.metrics = {
        'activated_checkers': activated,
        'templates': total,
        'killed': len(killed),
        'survived': len(survived),
        'false_alarm': len(false_alarm),
        'skipped': len(skipped),
        'evaluated': evaluated,
        'fn_rate': round(fn_rate, 4),
        'detection_coverage': round(len(killed) / total, 4) if total else 0.0,
    }
    if evaluated:
        result.score = round(100 * (1 - fn_rate))
        result.status = 'pass' if fn_rate <= _PROBE_FN_RATE_LIMIT else 'fail'
    else:
        result.score = 0
        result.status = 'warn'
    result.summary = (
        f'漏报探针 {total} 模板：检出 {len(killed)}，漏报 {len(survived)}，'
        f'误报否决 {len(false_alarm)}，跳过 {len(skipped)}；'
        f'漏报率 {fn_rate:.1%}')
    if not evaluated:
        result.summary += '；无有效评估，结果不可判定'
    for outcome in outcomes:
        if outcome['verdict'] in ('survived', 'false_alarm'):
            result.findings.append(_probe_finding(outcome))
_FN_PROBE_CACHE: dict[str, tuple[tuple, Any]] = {}
_FN_PROBE_CACHE_LOCK = threading.Lock()
_PROBE_FINGERPRINT_SKIP_DIRS_LOWER = (
    GENERIC_SCAN_IGNORE_DIRS_LOWER | CACHE_TEMP_DIR_NAMES)
def _skill_probe_fingerprint(skill_dir: str) -> tuple:
    """技能指纹：源码与 SKILL.md 内容 + 已激活历史模板内容。

    不能用 ``evolution_state.json`` 的 mtime——探针每次都会写
    ``fn_probe_history``，那样指纹永远变、缓存永远不命中。只哈希实际
    参与探针的源码和模板，既避免自写历史污染，也覆盖原地内容编辑。
    """
    code_digest = hashlib.sha256()
    for root, dirs, files in os.walk(skill_dir):
        dirs[:] = sorted(
            d for d in dirs
            if not is_pruned_scan_dir(d, _PROBE_FINGERPRINT_SKIP_DIRS_LOWER))
        for name in sorted(files):
            if name != "SKILL.md" and not is_py_source_file(name):
                continue
            path = os.path.join(root, name)
            rel_path = os.path.relpath(path, skill_dir).replace(os.sep, "/")
            try:
                digest = file_content_digest(path)
            except OSError as exc:
                _log.debug("[FN_Probe] 指纹源码读取失败: %s", exc)
                digest = f"unreadable:{type(exc).__name__}"
            code_digest.update(rel_path.encode("utf-8", "surrogatepass"))
            code_digest.update(b"\0")
            code_digest.update(digest.encode("ascii"))
            code_digest.update(b"\0")
    template_hash = ""
    try:
        from jwsgj.runtime_paths import read_evolution_section

        document = read_evolution_section(skill_dir, "probe_templates", {})
        entries = (document.get("templates")
                   if isinstance(document, dict) else None)
        active_entries = [
            item for item in (entries or [])
            if isinstance(item, dict) and item.get("active")]
        if active_entries:
            template_hash = hashlib.sha256(json.dumps(
                active_entries, ensure_ascii=False, sort_keys=True,
                separators=(",", ":"), default=str,
            ).encode("utf-8")).hexdigest()
    except (ImportError, OSError, ValueError, TypeError) as exc:
        _log.debug("[FN_Probe] 指纹未包含模板变更: %s", exc)
    return (code_digest.hexdigest(), template_hash)
def run_cached_false_negative_probe(skill_dir: str) -> TestMethodResult:
    """带进程内缓存的漏报探针（按技能指纹失效）。

    只缓存“成功跑完”的结果：异常不缓存，避免把一次性故障固化为长期盲区。
    """
    key = os.path.normcase(os.path.abspath(skill_dir))
    fingerprint = _skill_probe_fingerprint(skill_dir)
    with _FN_PROBE_CACHE_LOCK:
        cached = _FN_PROBE_CACHE.get(key)
    if cached is not None and cached[0] == fingerprint:
        _log.debug(
            "[FN_Probe] 命中缓存（指纹 %s）: %s", fingerprint, skill_dir)
        return copy.deepcopy(cached[1])
    result = run_false_negative_probe(skill_dir)
    with _FN_PROBE_CACHE_LOCK:
        _FN_PROBE_CACHE[key] = (fingerprint, copy.deepcopy(result))
    return result


def run_false_negative_probe(skill_dir: str, **kwargs) -> TestMethodResult:
    """漏报注入探针：注入已知缺陷 → 跑期望检测器 → 未检出即漏报。

    与 run_mutation_tests 方向相反：突变测试验证“已有 finding 是否
    真实”（降误报），本探针验证“已知缺陷是否被检出”（降漏报）。
    两者价值不重叠，互为补角。

    探针同时执行“激活”：对未接线的固化 checker 按需注册，并用无
    缺陷对照样本否决“能报但不准”的规则。
    """
    start = time.perf_counter()
    result = TestMethodResult(
        method_name=_PROBE_METHOD_NAME, method_id=_PROBE_METHOD_ID)
    if not skill_dir:
        result.status = 'skip'
        result.score = 0
        result.summary = 'skill_dir 为空，跳过漏报探针'
        return result.finish(start)
    try:
        activated = _probe_authority_ready()
    except Exception as exc:  # noqa: BLE001 — 装权失败降级为全量漏报
        log_swallowed(
            __name__, exc, context='false_negative_probe:authority')
        activated = 0
    outcomes = [_probe_one(tpl) for tpl in _all_probe_templates(skill_dir)]
    _apply_probe_outcome(result, outcomes, activated)
    result.metrics['persisted'] = _persist_probe_activations(
        skill_dir, outcomes)
    return result.finish(start)
def run_mutation_tests(skill_dir: str, **kwargs) -> TestMethodResult:
    start = time.perf_counter()
    result = TestMethodResult(
        method_name="突变测试",
        method_id="mutation_test",
    )
    if not isinstance(skill_dir, str) or not skill_dir.strip():
        return TestMethodResult.invalid_input(
            skill_dir, "突变测试", "mutation_test", "测试", start)
    skill_dir = os.path.abspath(skill_dir)
    if not os.path.isdir(skill_dir):
        return TestMethodResult.invalid_input(
            skill_dir, "突变测试", "mutation_test", "测试", start)
    cache = kwargs.get('_cache')
    if (cache is None or not hasattr(cache, 'valid_entries')
            or not _cache_owner_matches(cache, skill_dir)):
        if cache is not None:
            _log.warning(
                "[TestQuality] 忽略不可用或归属不匹配的缓存入参(%s)，"
                "按当前技能根重建", type(cache).__name__)
        cache = FileCache(skill_dir)
        cache.load()
    test_map = build_mutation_test_mapping(skill_dir)
    all_mutants = generate_mutants(
        cache, test_map, _GLOBAL_MUTATION_BUDGET, _PER_FILE_MUTATION_BUDGET)
    if not all_mutants:
        result.status = "skip"
        result.score = 0
        result.summary = "未生成任何有效突变体（无执行证据，不计分）"
        return result.finish(start)
    preskip_results, all_mutants = _preskip_low_confidence(all_mutants)
    effective_workers, eval_results = _runtime.run_mutation_batch(
        all_mutants, skill_dir, _runtime.MUTATION_TIMEOUT)
    eval_results.extend(preskip_results)
    _apply_mutation_summary(
        result, eval_results, len(preskip_results), effective_workers)
    return result.finish(start)
def _split_scored_results(eval_results) -> tuple[list, list]:
    scored = []
    inconclusive = []
    for r in eval_results:
        (inconclusive if r.get('error') else scored).append(r)
    return scored, inconclusive
def _apply_mutation_summary(result: TestMethodResult, eval_results: list,
                            preskip_count: int, num_workers: int) -> None:
    generated = len(eval_results)
    scored, inconclusive = _split_scored_results(eval_results)
    preskipped_files = sorted({
        r['rel_path'] for r in inconclusive
        if r.get('error') == _PRESKIP_ERROR})
    evaluated = len(scored)
    detected = sum(1 for r in scored if r['killed'])
    mutation_score = (detected / evaluated * 100) if evaluated > 0 else 0
    per_file = _per_file_mutation_stats(scored)
    result.findings = _per_file_score_findings(per_file)
    file_findings_total = len(per_file)
    files_with_mutations = len({r['rel_path'] for r in eval_results})
    result.metrics = {
        "mutations_generated": generated,
        "mutations_evaluated": evaluated,
        "mutations_detected": detected,
        "mutations_survived": evaluated - detected,
        "mutations_inconclusive": len(inconclusive),
        "mutation_score": round(mutation_score, 1),
        "files_with_mutations": files_with_mutations,
        "mutation_file_findings_reported": len(result.findings),
        "mutation_file_findings_truncated": max(
            0, file_findings_total - len(result.findings)),
        "parallel_workers": num_workers,
        "global_budget": _GLOBAL_MUTATION_BUDGET,
        "per_file_budget": _PER_FILE_MUTATION_BUDGET,
        "test_execution_mode": "pytest_batched",
        "preskipped_mutations": preskip_count,
        "preskip_rate": round(preskip_count / max(generated, 1) * 100, 1),
    }
    if preskipped_files:
        result.findings.append({
            "type": "mutation_uncovered_by_tests", "severity": "medium",
            "message": (
                f"{preskip_count} 个突变体所属模块仅有导入冒烟测试覆盖"
                f"（{len(preskipped_files)} 个文件，如 {preskipped_files[0]}），"
                "未进入执行评估；这些模块缺少行为断言测试"),
        })
    if evaluated == 0:
        result.status = "warn"
        result.score = 0
        reason = ([f"{preskip_count} 个仅有导入冒烟测试覆盖"]
                  if preskip_count else [])
        if len(inconclusive) - preskip_count:
            reason.append(
                f"{len(inconclusive) - preskip_count} 个因测试收集/环境错误")
        result.summary = (
            f"无可评估突变体：{len(inconclusive)} 个突变体未得到执行评估"
            f"（{'；'.join(reason) if reason else '无可用测试'}）")
        result.findings.append({
            "type": "mutation_inconclusive", "severity": "medium",
            "message": "全部突变体均未得到正常测试评估（收集错误/超时/环境不可用/"
                       "仅冒烟覆盖），突变分数不具判定力",
        })
        return
    if mutation_score < 30:
        result.status = "warn"
        result.score = 50
        result.summary = f"突变分数 {mutation_score:.1f}% — 大部分突变可存活，测试覆盖不足"
        result.findings.append({
            "type": "low_mutation_score", "severity": "medium",
            "message": f"突变分数 {mutation_score:.1f}%，建议增加测试以检测更多突变",
        })
        return
    result.status = "pass"
    result.score = 80
    result.summary = (f"突变分数 {mutation_score:.1f}% "
                      f"({detected}/{evaluated})")
    if inconclusive:
        result.summary += f"，{len(inconclusive)} 个不可判定"
@dataclass(frozen=True)
class _FileMutationContext:
    entry: object
    rel_path: str
    test_map: dict
    source_lines: list[str]
    docstring_nodes: frozenset
@dataclass(frozen=True)
class _MutantSpec:
    line_idx: int
    node: ast.AST
    old_text: str
    new_text: str
    scope: tuple[int, int] | None
def _utf8_byte_to_char(line: str, byte_offset: int) -> int | None:
    if byte_offset < 0:
        return None
    try:
        return len(line.encode('utf-8')[:byte_offset].decode('utf-8'))
    except UnicodeDecodeError as _e:
        log_swallowed(__name__, _e, context='_utf8_byte_to_char:UnicodeDecodeError')
        return None
def _node_scope(node: ast.AST, line: str) -> tuple[int, int] | None:
    if node.end_lineno != node.lineno:
        return None
    if line.isascii():
        start, end = node.col_offset, node.end_col_offset
    else:
        start = _utf8_byte_to_char(line, node.col_offset)
        end = _utf8_byte_to_char(line, node.end_col_offset)
    if not _valid_same_line_span(line, start, end):
        return None
    return start, end
_COMPARE_OP_MUTATIONS = {
    '<=': '<', '>=': '>',
    '<': '<=', '>': '>=',
    '==': '!=', '!=': '==',
}
_COMPARE_BRACKETS = frozenset('()[]{}')
_COMPARE_OP_TOKENS = tuple(sorted(
    _COMPARE_OP_MUTATIONS, key=lambda t: (-len(t), t)))
def _scan_compare_op_after(seg: str) -> tuple[int, int, str] | None:
    i = 0
    while i < len(seg) and (seg[i].isspace() or seg[i] in _COMPARE_BRACKETS):
        i += 1
    for _tok in _COMPARE_OP_TOKENS:
        if seg.startswith(_tok, i):
            return i, i + len(_tok), _tok
    return None
def _scan_compare_op_before(seg: str) -> tuple[int, int, str] | None:
    j = len(seg)
    while j > 0 and (seg[j - 1].isspace() or seg[j - 1] in _COMPARE_BRACKETS):
        j -= 1
    for _tok in _COMPARE_OP_TOKENS:
        _s = j - len(_tok)
        if _s >= 0 and seg[_s:j] == _tok:
            return _s, j, _tok
    return None
def _locate_compare_op_same_line(
    lop, rop, seg_line: str,
) -> tuple[tuple[int, int], str] | None:
    _s = _utf8_byte_to_char(seg_line, lop.end_col_offset)
    _e = _utf8_byte_to_char(seg_line, rop.col_offset)
    if not _valid_same_line_span(seg_line, _s, _e):
        return None
    _hit = _scan_compare_op_after(seg_line[_s:_e])
    if _hit is None:
        return None
    _hs, _he, _tok = _hit
    if not _only_blanks_or_brackets(seg_line[_s + _he:_e]):
        return None
    return (_s + _hs, _s + _he), _tok
def _valid_same_line_span(seg_line: str, start: int | None,
                          end: int | None) -> bool:
    if start is None or end is None:
        return False
    return 0 <= start < end <= len(seg_line)
def _only_blanks_or_brackets(text: str) -> bool:
    return all(c.isspace() or c in _COMPARE_BRACKETS for c in text)
def _locate_compare_op_cross_line(
    lop, rop, source_lines: list[str], lop_end_ln: int, rop_ln: int,
) -> tuple[int, tuple[int, int], str] | None:
    _lop_line = source_lines[lop_end_ln - 1]
    _s = _utf8_byte_to_char(_lop_line, lop.end_col_offset)
    if _s is not None:
        _hit = _scan_compare_op_after(_lop_line[_s:])
        if _hit is not None:
            _hs, _he, _tok = _hit
            return lop_end_ln - 1, (_s + _hs, _s + _he), _tok
    for _line_no in range(lop_end_ln + 1, rop_ln):
        _hit = _scan_compare_op_after(source_lines[_line_no - 1])
        if _hit is not None:
            _hs, _he, _tok = _hit
            return _line_no - 1, (_hs, _he), _tok
    _rop_line = source_lines[rop_ln - 1]
    _e = _utf8_byte_to_char(_rop_line, rop.col_offset)
    if _e is not None:
        _hit = _scan_compare_op_before(_rop_line[:_e])
        if _hit is not None:
            _hs, _he, _tok = _hit
            return rop_ln - 1, (_hs, _he), _tok
    return None
def _locate_compare_op(
    lop, rop, source_lines: list[str],
) -> tuple[int, tuple[int, int], str] | None:
    _lop_end_ln = getattr(lop, 'end_lineno', None)
    _rop_ln = getattr(rop, 'lineno', None)
    if not (isinstance(_lop_end_ln, int) and isinstance(_rop_ln, int)
            and 0 < _lop_end_ln <= len(source_lines)
            and 0 < _rop_ln <= len(source_lines)):
        return None
    if _lop_end_ln != _rop_ln:
        return _locate_compare_op_cross_line(
            lop, rop, source_lines, _lop_end_ln, _rop_ln)
    _hit = _locate_compare_op_same_line(
        lop, rop, source_lines[_lop_end_ln - 1])
    if _hit is None:
        return None
    return _lop_end_ln - 1, _hit[0], _hit[1]
def _file_mutation_ctx(entry, test_map: dict):
    basename = os.path.basename(entry.path)
    if is_test_source_basename(basename) or basename == '__init__.py':
        return None
    rel_path = entry.rel_path.replace(os.sep, '/')
    if rel_path not in test_map:
        return None
    source_lines = entry.source.split('\n')
    docstring_nodes = _collect_docstring_nodes(entry.tree)
    return _FileMutationContext(
        entry=entry, rel_path=rel_path, test_map=test_map,
        source_lines=source_lines, docstring_nodes=docstring_nodes,
    ), entry.tree
def _build_mutant(file_ctx: _FileMutationContext, spec: _MutantSpec):
    line_idx = spec.line_idx
    line = file_ctx.source_lines[line_idx]
    scope = spec.scope
    check_seg = _segment_of(line, scope)
    if not spec.old_text or spec.old_text not in check_seg:
        return None
    if _is_equivalent_mutation(spec.node, file_ctx.docstring_nodes):
        return None
    mutated_source = _spliced_source(file_ctx.source_lines, spec)
    try:
        compile(mutated_source, f"{file_ctx.rel_path}:{line_idx + 1}", 'exec')
    except (SyntaxError, ValueError) as e:
        _log.warning("[TestQuality] 生成变异解析失败,跳过: %s", e)
        return None
    mapping_entry = file_ctx.test_map[file_ctx.rel_path]
    return {
        'rel_path': file_ctx.rel_path,
        'line': line_idx + 1,
        'mutated': mutated_source,
        'test_files': list(mapping_entry.get('test_files') or ()),
        'mapping_confidence': mapping_entry.get(
            'confidence', _DEFAULT_MAPPING_CONFIDENCE),
        'mutation_type': type(spec.node).__name__,
    }
def _segment_of(line: str, scope) -> str:
    return line[scope[0]:scope[1]] if scope is not None else line
def _node_segment(node, line: str) -> tuple:
    scope = _node_scope(node, line)
    return scope, _segment_of(line, scope)
def _spliced_source(source_lines: list[str], spec: _MutantSpec) -> str:
    line_idx = spec.line_idx
    line = source_lines[line_idx]
    if spec.scope is None:
        mutated_line = line.replace(spec.old_text, spec.new_text, 1)
    else:
        start, end = spec.scope
        mutated_line = (line[:start]
                        + line[start:end].replace(spec.old_text, spec.new_text, 1)
                        + line[end:])
    return '\n'.join(
        source_lines[:line_idx] + [mutated_line] + source_lines[line_idx + 1:])
_STR_MUTATION_MAX_LEN = 80
def _constant_literal_source(value, seg: str) -> str | None:
    literal = seg.strip()
    if not literal:
        return None
    try:
        if ast.literal_eval(literal) != value:
            return None
    except (ValueError, SyntaxError, TypeError, MemoryError, RecursionError) as _swallowed_exc:
        log_swallowed(
            __name__, _swallowed_exc,
            context=f'_constant_literal_source:{type(_swallowed_exc).__name__}')
        return None
    return literal
def _constant_int_pair(value: int, seg: str) -> tuple[str, str] | None:
    literal = _constant_literal_source(value, seg)
    return (literal, str(value + 1)) if literal is not None else None
def _constant_str_pair(value: str, seg: str) -> tuple[str, str] | None:
    if not 0 < len(value) < _STR_MUTATION_MAX_LEN:
        return None
    literal = _constant_literal_source(value, seg)
    return (literal, "''") if literal is not None else None
def _constant_mutation_pair(value, seg: str) -> tuple[str, str] | None:
    if isinstance(value, bool):
        return ('True', 'False') if value else ('False', 'True')
    if isinstance(value, int):
        return _constant_int_pair(value, seg)
    if isinstance(value, str):
        return _constant_str_pair(value, seg)
    return None
def _constant_mutants(node: ast.Constant, line: str, line_idx: int,
                      _build) -> list:
    _scope, _seg = _node_segment(node, line)
    _pair = _constant_mutation_pair(node.value, _seg)
    if _pair is None:
        return []
    old, new = _pair
    _mutant = _build(_MutantSpec(line_idx, node, old, new, _scope))
    return [_mutant] if _mutant is not None else []
def _return_mutants(node: ast.Return, line: str, line_idx: int,
                    _build) -> list:
    if (node.value is None
            or (isinstance(node.value, ast.Constant)
                and node.value.value is None)):
        return []
    if node.end_lineno != node.lineno:
        return []
    _scope, _ret_seg = _node_segment(node, line)
    m = re.search(r'return\b\s*', _ret_seg)
    if not m:
        return []
    _mutant = _build(_MutantSpec(
        line_idx, node, m.group(0), 'return None  # MUTATED ', _scope))
    return [_mutant] if _mutant is not None else []
def _compare_mutants(node: ast.Compare, source_lines: list, _build) -> list:
    _mutants = []
    _operands = [node.left, *node.comparators]
    for _op, _lop, _rop in zip(
            node.ops, _operands[:-1], _operands[1:], strict=True):
        _loc = _locate_compare_op(_lop, _rop, source_lines)
        if _loc is None:
            continue
        _op_line_idx, (_op_s, _op_e), _op_tok = _loc
        _new_tok = _COMPARE_OP_MUTATIONS.get(_op_tok)
        if not _new_tok:
            continue
        _mutant = _build(_MutantSpec(
            _op_line_idx, node, _op_tok, _new_tok, (_op_s, _op_e)))
        if _mutant is not None:
            _mutants.append(_mutant)
    return _mutants
def _mutation_budget_left(file_count: int, total_count: int,
                          per_file_budget: int, global_budget: int) -> int:
    return max(0, min(per_file_budget - file_count,
                      global_budget - total_count))
def _node_mutant_batch(node, source_lines: list, _build) -> list:
    if not isinstance(node, (ast.Constant, ast.Compare, ast.Return)):
        return []
    line_idx = node.lineno - 1
    if not 0 <= line_idx < len(source_lines):
        return []
    line = source_lines[line_idx]
    if isinstance(node, ast.Compare):
        return _compare_mutants(node, source_lines, _build)
    if isinstance(node, ast.Constant):
        return _constant_mutants(node, line, line_idx, _build)
    return _return_mutants(node, line, line_idx, _build)
def _file_mutants(file_ctx, tree, all_mutants: list,
                  global_budget: int, per_file_budget: int) -> None:
    def _build(spec: _MutantSpec):
        return _build_mutant(file_ctx, spec)
    source_lines = file_ctx.source_lines
    file_mutants = 0
    for node in walk_nodes(tree):
        capacity = _mutation_budget_left(
            file_mutants, len(all_mutants), per_file_budget, global_budget)
        if capacity == 0:
            break
        batch = _node_mutant_batch(node, source_lines, _build)[:capacity]
        all_mutants.extend(batch)
        file_mutants += len(batch)
def generate_mutants(cache, test_map: dict, global_budget: int, per_file_budget: int) -> list:
    all_mutants = []
    for entry in cache.valid_entries:
        if len(all_mutants) >= global_budget:
            break
        prepared = _file_mutation_ctx(entry, test_map)
        if prepared is None:
            continue
        file_ctx, tree = prepared
        _file_mutants(file_ctx, tree, all_mutants, global_budget, per_file_budget)
    return all_mutants
def _docstring_constant_nodes(tree: ast.AST) -> list[ast.Constant]:
    return [
        node.value for node in walk_nodes(tree)
        if (isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str))
    ]
def _collect_docstring_nodes(tree: ast.AST) -> frozenset:
    return frozenset(id(node) for node in _docstring_constant_nodes(tree))
def _is_equivalent_mutation(node: ast.AST,
                            docstring_nodes: frozenset) -> bool:
    return id(node) in docstring_nodes
MAX_VERIFY_COUNT = 10
SAFETY_RULE_KEYWORDS = (
    "security", "injection", "xss", "sql", RULE_COMMAND_INJECTION,
    "path_traversal", "csrf", "ssrf", RULE_HARDCODED_SECRET, "unsafe_eval",
)
COMPLEXITY_RULE_KEYWORDS = (
    "complexity", "cognitive", "cyclomatic", "nested_depth", "param_count",
)
@dataclass
class MutationResult:
    locator: str
    rule_id: str
    file: str
    line: int
    target_type: str = ""
    target_name: str = ""
    tests_passed: bool = False
    tests_ran: int = 0
    tests_failed: int = 0
    error: str = ""
    is_confirmed_dead: bool = False
    elapsed_ms: float = 0.0
    def to_dict(self) -> dict:
        return {
            "locator": self.locator,
            "rule_id": self.rule_id,
            "file": self.file,
            "line": self.line,
            "target_type": self.target_type,
            "target_name": self.target_name,
            "tests_passed": self.tests_passed,
            "tests_ran": self.tests_ran,
            "tests_failed": self.tests_failed,
            "is_confirmed_dead": self.is_confirmed_dead,
            "error": self.error,
            "elapsed_ms": round(self.elapsed_ms, 1),
        }
@dataclass
class MutationReport:
    total_verified: int = 0
    confirmed_dead: int = 0
    false_positive: int = 0
    skipped: int = 0
    errors: int = 0
    results: dict[str, MutationResult] = field(default_factory=dict)
def _matches_keyword(combined: str, keywords) -> bool:
    return any(kw in combined for kw in keywords)
def classify_finding_type(f: dict) -> str:
    if is_dead_code_finding(f.get("rule_id") or "", f):
        return "dead_code"
    _rid_raw = f.get("rule_id") or ""
    _rf_raw = f.get("rule_family") or ""
    candidates = (_rid_raw, _rf_raw)
    if any(matches_rule_family(c, "security") for c in candidates):
        return "safety"
    if any(matches_rule_family(c, "complexity") for c in candidates):
        return "complexity"
    combined = f"{str(_rid_raw).lower()} {str(_rf_raw).lower()}"
    if _matches_keyword(combined, SAFETY_RULE_KEYWORDS):
        return "safety"
    if _matches_keyword(combined, COMPLEXITY_RULE_KEYWORDS):
        return "complexity"
    return "skip"
_MUTATION_VERDICT_FIELDS = (
    SIGNAL_MUTATION_VERIFIED,
    SIGNAL_MUTATION_CONFIRMED_DEAD,
    "_mutation_tests_passed",
    "_mutation_tests_failed",
    "_mutation_inconclusive",
    "_mutation_skipped",
    "_mutation_not_applicable",
)
_MUTATION_ANNOTATION_FIELDS = (
    "_mutation_annotation_done",
    "_mutation_safety_has_tests",
    "_mutation_complexity_score",
)
_ANNOTATION_TARGETS = ("safety_annotation", "complexity_annotation")
def _clear_mutation_fields(f: dict, fields: Iterable[str]) -> None:
    for key in fields:
        f.pop(key, None)
def _apply_mutation_result(f: dict, r: MutationResult) -> None:
    _clear_mutation_fields(f, _MUTATION_VERDICT_FIELDS)
    if r.target_type in _ANNOTATION_TARGETS:
        if r.error:
            _clear_mutation_fields(f, _MUTATION_ANNOTATION_FIELDS)
        elif r.target_type == "safety_annotation":
            f.pop("_mutation_complexity_score", None)
        else:
            f.pop("_mutation_safety_has_tests", None)
        f["_mutation_annotation_done"] = not r.error
        f["_mutation_tests_passed"] = r.tests_passed
        f["_mutation_tests_failed"] = r.tests_failed
        f["_mutation_inconclusive"] = bool(r.error)
    else:
        _clear_mutation_fields(f, _MUTATION_ANNOTATION_FIELDS)
        f[SIGNAL_MUTATION_VERIFIED] = True
        f[SIGNAL_MUTATION_CONFIRMED_DEAD] = r.is_confirmed_dead
        f["_mutation_tests_passed"] = r.tests_passed
        f["_mutation_tests_failed"] = r.tests_failed
        f["_mutation_inconclusive"] = bool(r.error)
def _mark_mutation_not_verified(f: dict) -> None:
    _clear_mutation_fields(f, _MUTATION_VERDICT_FIELDS)
    _clear_mutation_fields(f, _MUTATION_ANNOTATION_FIELDS)
    f[SIGNAL_MUTATION_VERIFIED] = False
    f[SIGNAL_MUTATION_CONFIRMED_DEAD] = False
    f["_mutation_tests_passed"] = False
    f["_mutation_tests_failed"] = 0
    ftype = classify_finding_type(f)
    if ftype == "skip":
        f["_mutation_not_applicable"] = True
    else:
        f["_mutation_skipped"] = True
def annotate_findings_with_mutation(
    findings: list[dict],
    mutation_report: MutationReport,
) -> list[dict]:
    try:
        if not isinstance(mutation_report, MutationReport):
            _log.warning("[annotate_findings_with_mutation] 非 MutationReport 输入(%s)，跳过注解",
                         type(mutation_report).__name__)
            return findings
        items = dict_findings(findings)
        pairs: list[tuple[dict, MutationResult | None]] = []
        for f in items:
            try:
                locator = make_locator_fast(f)
            except (AttributeError, TypeError, KeyError, ValueError) as exc:
                _log.warning(
                    "[annotate_findings_with_mutation] 定位符解析失败"
                    "（保持未标注）: %s", exc)
                continue
            pairs.append((f, mutation_report.results.get(locator)))
        for f, r in pairs:
            try:
                if r is not None:
                    _apply_mutation_result(f, r)
                else:
                    _mark_mutation_not_verified(f)
            except (AttributeError, TypeError, KeyError, ValueError) as exc:
                _log.warning(
                    "[annotate_findings_with_mutation] 单条注解失败"
                    "（保持未标注）: %s", exc)
        return list(findings) if isinstance(findings, (list, tuple)) else items
    except Exception:
        _log.exception("[annotate_findings_with_mutation] 异常降级")
        return findings
def _identity_result(locator: str, identity: tuple[str, str, int],
                     target_type: str = "", target_name: str = "",
                     **fields: Any) -> MutationResult:
    rule_id, file, line = identity
    return MutationResult(
        locator=locator,
        rule_id=rule_id,
        file=file,
        line=line,
        target_type=target_type,
        target_name=target_name,
        **fields,
    )
def _finding_identity(finding: dict) -> tuple[str, str, int]:
    rule_id = str(finding.get("rule_id") or "")
    return rule_id, finding_file_path(finding), safe_finding_line(finding)
def _cached_mutation_result(cached: dict, locator: str,
                            identity: tuple[str, str, int],
                            func_name: str) -> MutationResult:
    tests_passed = cached.get("tests_passed", False) is True
    error = cached.get("error")
    if not isinstance(error, str):
        error = ""
    is_confirmed_dead = (
        cached.get("is_confirmed_dead", False) is True
        and tests_passed and not error)
    return _identity_result(
        locator, identity,
        target_type=cached.get("target_type", ""),
        target_name=func_name,
        tests_passed=tests_passed,
        tests_ran=safe_int(cached.get("tests_ran"), 0),
        tests_failed=safe_int(cached.get("tests_failed"), 0),
        is_confirmed_dead=is_confirmed_dead,
        error=error,
        elapsed_ms=finite_float_or_zero(cached.get("elapsed_ms")),
    )
def _verdict_bucket(result: MutationResult) -> str | None:
    if result.error:
        return "errors"
    if result.is_confirmed_dead:
        return "confirmed_dead"
    if result.target_type in _ANNOTATION_TARGETS:
        return None
    return "false_positive"
def _tally_verdict(report: MutationReport, result: MutationResult,
                   delta: int) -> None:
    bucket = _verdict_bucket(result)
    if bucket is not None:
        setattr(report, bucket, getattr(report, bucket) + delta)
def _record_verify_result(report: MutationReport, locator: str,
                          result: MutationResult) -> None:
    previous = report.results.get(locator)
    if previous is not None:
        _tally_verdict(report, previous, -1)
        report.total_verified -= 1
    report.results[locator] = result
    _tally_verdict(report, result, 1)
    report.total_verified += 1
def _record_verify_error(report: MutationReport, finding: dict,
                         error: str, target_type: str = "") -> None:
    try:
        locator = make_locator_fast(finding)
        identity = _finding_identity(finding)
    except (AttributeError, TypeError, KeyError, ValueError, RuntimeError) as exc:
        _log.warning("[Mutation] 错误结果登记失败（finding 身份不可解析）: %s",
                     exc)
        report.errors += 1
        report.total_verified += 1
        return
    _record_verify_result(report, locator, _identity_result(
        locator, identity, target_type=target_type, error=error))
def _mutation_target(func_name: str, start_line: int, end_line: int,
                     line: int) -> tuple[str, int, int]:
    if func_name and end_line > start_line:
        return _runtime.REMOVE_FUNCTION, start_line, end_line
    return _runtime.REMOVE_LINE, line, line
def _annotation_source_readable(filepath: str) -> bool:
    try:
        read_source_text_strict(filepath)
        return True
    except (OSError, UnicodeError, SyntaxError, ValueError) as e:
        _log.warning(
            "[Mutation] 注解目标源码不可读（判不可判定）: %s: %s", filepath, e)
        return False
def _record_annotation_failure(report: MutationReport, f: dict, ftype: str,
                               locator: str,
                               identity: tuple[str, str, int],
                               error: str) -> None:
    _clear_mutation_fields(f, _MUTATION_ANNOTATION_FIELDS)
    f["_mutation_annotation_done"] = False
    _record_verify_result(report, locator, _identity_result(
        locator, identity, target_type=f"{ftype}_annotation", error=error))
class MutationVerifier:
    def __init__(self, skill_dir: str, timeout: int = _runtime.MUTATION_TIMEOUT):
        if isinstance(skill_dir, str) and not skill_dir.strip():
            raise ValueError("skill_dir 不能为空或纯空白")
        self.skill_dir = os.path.abspath(skill_dir)
        self.timeout = timeout
        self._cache = _runtime.MutationResultCache(self.skill_dir)
        self._test_map: dict | None = None
    def _mutation_test_map(self) -> dict:
        if self._test_map is None:
            self._test_map = build_mutation_test_mapping(self.skill_dir)
        return self._test_map
    def _annotate_lightweight(self, f: dict, ftype: str, locator: str,
                              identity: tuple[str, str, int],
                              report: MutationReport) -> None:
        _clear_mutation_fields(f, _MUTATION_ANNOTATION_FIELDS)
        _, f_file, line = identity
        _filepath = os.path.join(self.skill_dir, f_file)
        if ftype == "safety":
            if not _annotation_source_readable(_filepath):
                _record_annotation_failure(
                    report, f, ftype, locator, identity,
                    "annotation_source_unreadable_inconclusive")
                return
            annotate_safety_finding(f, _filepath)
            if "_mutation_safety_has_tests" not in f:
                _record_annotation_failure(
                    report, f, ftype, locator, identity,
                    "annotation_not_applied_inconclusive")
                return
            tests_passed = f.get("_mutation_safety_has_tests") is True
        else:
            if not _annotation_source_readable(_filepath):
                _record_annotation_failure(
                    report, f, ftype, locator, identity,
                    "annotation_source_unreadable_inconclusive")
                return
            annotate_complexity_finding(f, _filepath, line)
            score = f.get("_mutation_complexity_score")
            if (f.get("_mutation_annotation_done") is not True
                    or isinstance(score, bool) or not isinstance(score, int)
                    or score < 0):
                _record_annotation_failure(
                    report, f, ftype, locator, identity,
                    "complexity_annotation_unavailable_inconclusive")
                return
            tests_passed = True
        _record_verify_result(report, locator, _identity_result(
            locator, identity,
            target_type=f"{ftype}_annotation",
            tests_passed=tests_passed,
        ))
    def _validate_one(self, f: dict, report: MutationReport,
                      ftype: str) -> None:
        target_hint = (f"{ftype}_annotation"
                       if ftype in ("safety", "complexity") else "")
        try:
            locator = make_locator_fast(f)
            identity = _finding_identity(f)
            _, _f_file, line = identity
            filepath = os.path.join(self.skill_dir, _f_file)
            path_safe, path_error = check_path_traversal(self.skill_dir, filepath)
            if not path_safe:
                _record_verify_result(report, locator, _identity_result(
                    locator, identity, target_type=target_hint,
                    error=f"path_escape_inconclusive: {path_error}"))
                return
            if not os.path.isfile(filepath):
                _record_verify_error(
                    report, f, "target_file_missing_inconclusive", target_hint)
                return
            if ftype == "safety":
                self._annotate_lightweight(f, ftype, locator, identity, report)
                return
            if line <= 0:
                _record_verify_error(
                    report, f, "invalid_line_inconclusive", target_hint)
                return
            if ftype == "complexity":
                self._annotate_lightweight(f, ftype, locator, identity, report)
                return
            func_name, start_line, end_line = find_function_boundary(
                filepath, line
            )
            target_type, start, end = _mutation_target(
                func_name, start_line, end_line, line)
            result = self._verify_single(
                filepath, locator, f, func_name,
                target_type, start, end,
            )
            _record_verify_result(report, locator, result)
        except Exception as exc:
            _log.exception(
                "[Mutation] 单 finding 验证异常, 计 errors 继续: "
                "ftype=%s finding=%s", ftype, type(f).__name__)
            _record_verify_error(
                report, f,
                f"verify_exception_inconclusive: {type(exc).__name__}",
                target_hint)
    @staticmethod
    def _severity_rank(f: dict) -> int:
        severity = f.get("severity")
        token = severity.upper().strip() if isinstance(severity, str) else "P3"
        return SEVERITY_RANK.get(token, 5)
    def _verifiable_targets(self, findings, report: MutationReport
                            ) -> list[tuple[dict, str, str]]:
        targets: list[tuple[dict, str, str]] = []
        for f in dict_findings(findings):
            try:
                ftype = classify_finding_type(f)
                locator = make_locator_fast(f) if ftype != "skip" else ""
            except Exception as exc:
                _log.warning(
                    "[Mutation] finding 分类/定位失败（按 error 记账并继续）: %r",
                    exc)
                _record_verify_error(
                    report, f,
                    f"classify_exception_inconclusive: {type(exc).__name__}")
                continue
            if ftype != "skip":
                targets.append((f, ftype, locator))
        return targets
    def validate(
        self,
        findings: list[dict],
        max_verify: int = MAX_VERIFY_COUNT,
    ) -> MutationReport:
        report = MutationReport()
        targets = self._verifiable_targets(findings, report)
        if not targets:
            _log.info("[Mutation] 无可验证 finding，跳过")
            return report
        self._cache.refresh_execution_fingerprint()
        self._test_map = None
        targets.sort(key=lambda pair: self._severity_rank(pair[0]))
        unique_targets = []
        seen_locators = set()
        for target in targets:
            locator = target[2]
            if locator in seen_locators:
                continue
            seen_locators.add(locator)
            unique_targets.append(target)
        budget = max(0, safe_int(max_verify, MAX_VERIFY_COUNT))
        selected = unique_targets[:budget]
        report.skipped = len(unique_targets) - len(selected)
        _log.info(
            "[Mutation] %d verifiable findings (%d unique locators), verifying %d",
            len(targets), len(unique_targets), len(selected))
        for f, ftype, _locator in selected:
            self._validate_one(f, report, ftype)
        _log.info(
            "[Mutation] 完成: %d verified, %d confirmed dead, %d FP, %d errors",
            report.total_verified, report.confirmed_dead,
            report.false_positive, report.errors)
        return report
    def _fingerprint_and_cached(self, filepath: str, locator: str,
                                identity: tuple[str, str, int],
                                func_name: str, target_type: str
                                ) -> tuple[int, str, MutationResult | None]:
        file_size = 0
        file_digest = ""
        try:
            file_size = os.path.getsize(filepath)
            file_digest = file_content_digest(filepath)
        except OSError as e:
            _log.warning("[Mutation] 文件 stat/hash 失败: %s", e, exc_info=True)
            return 0, "", _identity_result(
                locator, identity,
                target_type=target_type,
                target_name=func_name,
                error=f"file_stat_error: {e}",
            )
        cached = self._cache.get(locator, file_size, file_digest)
        if cached is not None:
            return file_size, file_digest, _cached_mutation_result(
                cached, locator, identity, func_name)
        return file_size, file_digest, None
    def _verify_single(
        self,
        filepath: str,
        locator: str,
        finding: dict,
        func_name: str,
        target_type: str,
        start_line: int,
        end_line: int,
    ) -> MutationResult:
        identity = _finding_identity(finding)
        file_size, file_md5, cached = self._fingerprint_and_cached(
            filepath, locator, identity, func_name, target_type)
        if cached is not None:
            return cached
        start_time = time.time()
        result = _identity_result(locator, identity, target_type, func_name)
        _env_error = False
        try:
            outcome = _runtime.probe_mutation(
                filepath, target_type, start_line, end_line, self.skill_dir,
                timeout=self.timeout, test_map=self._mutation_test_map())
            result.tests_passed = outcome.tests_passed
            result.tests_ran = outcome.tests_ran
            result.tests_failed = outcome.tests_failed
            result.error = outcome.error
            result.is_confirmed_dead = bool(
                outcome.tests_passed and not outcome.error)
            _env_error = outcome.env_error
        except (OSError, UnicodeError, ValueError, KeyError, RuntimeError) as e:
            result.error = f"verify_exception_inconclusive: {type(e).__name__}: {str(e)[:200]}"
            _log.warning("[Mutation] 验证失败 %s: %s", locator, e)
            _env_error = True
            return result
        except BaseException:
            _env_error = True
            raise
        finally:
            result.elapsed_ms = (time.time() - start_time) * MS_PER_SECOND
            if not _env_error:
                self._cache.put(locator, file_size, file_md5,
                                result.to_dict())
        return result

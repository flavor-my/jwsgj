from __future__ import annotations

import argparse
import ast
import contextlib
import json
import keyword
import logging
import os
import shlex
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, ClassVar, NoReturn


def _derive_app_name(package: str | None, module_name: str,
                     module_file: str) -> str:
    if package:
        return package.split(".", 1)[0]
    if module_name and module_name != "__main__":
        return module_name.split(".", 1)[0]
    return os.path.basename(os.path.dirname(os.path.abspath(module_file))) or "app"
def _split_windows_argv(text: str) -> list[str]:
    args: list[str] = []
    token: list[str] = []
    in_quotes = False
    token_started = False
    index = 0
    while index < len(text):
        char = text[index]
        if char in " \t" and not in_quotes:
            if token_started:
                args.append("".join(token))
                token = []
                token_started = False
            index += 1
            continue
        if char == "\\":
            slash_start = index
            while index < len(text) and text[index] == "\\":
                index += 1
            slash_count = index - slash_start
            if index >= len(text) or text[index] != '"':
                token.extend("\\" * slash_count)
                token_started = True
                continue
            token.extend("\\" * (slash_count // 2))
            token_started = True
            if slash_count % 2:
                token.append('"')
                index += 1
                continue
        if text[index] == '"':
            # 引号内 "" 是字面引号（CRT 规则），引号状态保持不变；
            # 退出引号模式会把后续空白误当分隔符（"a""b c" -> ['a"b', 'c']）
            if (in_quotes and index + 1 < len(text)
                    and text[index + 1] == '"'):
                token.append('"')
                token_started = True
                index += 2
                continue
            in_quotes = not in_quotes
            token_started = True
            index += 1
            continue
        token.append(text[index])
        token_started = True
        index += 1
    if token_started:
        args.append("".join(token))
    return args
def _split_argv_text(text: str) -> list[str]:
    try:
        if os.name == "nt":
            return _split_windows_argv(text)
        return shlex.split(text)
    except ValueError as e:
        raise ValueError(f"argv 字符串词法拆分失败: {e}") from e
def _normalize_argv(argv) -> list[str]:
    if argv is None:
        return sys.argv[1:]
    if isinstance(argv, str):
        return _split_argv_text(argv)
    if isinstance(argv, (list, tuple)):
        return list(argv)
    raise ValueError(
        f"argv 必须是 list/tuple/str/None，实际为 {type(argv).__name__}")
_JWSGJ_PARENT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _JWSGJ_PARENT not in sys.path:
    sys.path.insert(0, _JWSGJ_PARENT)
_PACKAGE_NAME = _derive_app_name(__package__, __name__, __file__)
_DEFAULT_OUTPUT_FORMAT = "json"
_DEFAULT_READ_ERROR_CODE = 2
import jwsgj.cli_skill_runtime as _skill_runtime
from jwsgj.build_contract import (
    DEFAULT_PROJECT_ROOT,
    cli_boundary,
    dump_json_report_checked,
    emit_json_report,
    fail_cli,
    field_of,
    finish_cli_command,
    json_text,
    load_json_file,
    norm_list,
    parse_csv_option,
    require_dict,
    require_dir,
    require_file,
    resolve_project_root,
    resolve_report_path,
    run_cli_action,
    split_csv,
    to_mapping,
)
from jwsgj.build_contract import exit_code_of as _exit_code_of
from jwsgj.build_refactor_gate import BatchQualityMonitor
from jwsgj.build_refactor_plan import estimate_splits
from jwsgj.build_refactor_policy import (
    REFACTOR_DISCIPLINE_COMMANDS,
    register_refactor_discipline,
)
from jwsgj.build_script_generation import (
    generate_agent_cli_template,
    generate_agent_module_template,
)
from jwsgj.cleanup_file_hygiene import print_report as _print_stub_report
from jwsgj.cleanup_file_hygiene import scan_stubs
from jwsgj.diag_blindspot_report import (
    DEFAULT_TOP_FILES,
    run_lightweight_diagnosis,
    scan_blindspots,
)
from jwsgj.diag_business_flow import DEFAULT_MAX_DEPTH, diagnose_business_flows
from jwsgj.diag_callgraph_builder import CallGraphBuilder
from jwsgj.diag_callgraph_verdicts import log_call_chain_summary
from jwsgj.diag_coverage_runtime import (
    DEFAULT_CACHE_MAX_AGE_S,
    DEFAULT_WAIT_TIMEOUT_S,
    DEFAULT_WORKERS,
)
from jwsgj.diag_coverage_scan import (
    DEFAULT_COVERAGE_THRESHOLD,
    scan_test_coverage,
)
from jwsgj.diag_delivery_gate import format_delivery_ci_output, run_full_delivery_gate
from jwsgj.diag_detector_assembly import (
    DiagnoseGate,
    quick_audit_pattern_check,
    to_gate_finding,
)
from jwsgj.diag_guard_dirfile import get_architecture_rules
from jwsgj.diag_guard_io import (
    atomic_write_text,
    guarded_open,
)
from jwsgj.diag_guard_state import (
    write_json_artifact,
)
from jwsgj.diag_incremental_review import (
    INCREMENTAL_REVIEW_COMMANDS,
    register_incremental_review,
)
from jwsgj.diag_method_invoke import run_full_runtime_analysis
from jwsgj.diag_runtime_forensics import install as guard_install
from jwsgj.diag_runtime_forensics import snapshot as guard_snapshot
from jwsgj.diag_runtime_forensics import status as guard_status
from jwsgj.diag_shared_source_core import read_source_with_fingerprint
from jwsgj.diag_solidify_rules import (
    DEFAULT_SOLIDIFY_MODE,
    SolidificationRegistry,
    SolidificationReport,
    SolidificationRuleGenerator,
    SolidifyMode,
    StaticSolidifier,
    collect_active_py_files,
    resolve_solidify_mode,
)
from jwsgj.diag_split_gate import quick_guard
from jwsgj.diag_split_plan import plan_split
from jwsgj.diag_taint_symbolic import (
    SymbolicExecutor,
    concolic_file_score,
    guided_concolic_explore,
)
from jwsgj.diag_testing_coverage import apply_coverage_extras, write_coverage_payload
from jwsgj.diag_types_normalize import normalize_passed
from jwsgj.diag_types_vocab import (
    DEFAULT_TASK_TYPE,
    FIELD_TOTAL_FUNCTIONS,
    MSG_EXCEPTION_BROAD_HANDLER,
)
from jwsgj.diag_wiring_symbol_scan import (
    ImportSafetyScanner,
    import_check_payload,
    print_import_chain_result,
    print_report,
    quick_check,
)
from jwsgj.diag_zero_backlog_gate import fanout_residual_gate
from jwsgj.engine_d1_tool_channels import (
    generate_source_exploit_report,
    quick_vulnerability_check,
)
from jwsgj.fanout_governance import (
    emit_fanout_html,
    run_fanout_diagnosis,
    verify_fanout_residual,
)
from jwsgj.fanout_report import FanoutConfig
from jwsgj.html_render_diag import render_blindspot_report_html
from jwsgj.html_render_pipeline import generate_html_report
from jwsgj.log_config import log_swallowed
from jwsgj.pipeline_steps_phases import resolve_fanout_diagnosis_inputs
from jwsgj.prevention_scope_facts import walk_nodes
from jwsgj.refactor_api_contract import CONTRACT_COMMANDS, register_cli_contract
from jwsgj.refactor_decompose_actions import attach_function_decomposition
from jwsgj.runtime_paths import resolve_skill_reference
from jwsgj.runtime_scope import PACKAGE_VERSION as __version__
from jwsgj.runtime_scope import collect_scan_py_files, is_test_file_path
from jwsgj.shared_cache import as_diag_ctx, get_warmed_cache, validated_warmed_root

logger = logging.getLogger("jwsgj.__main__")
_log = logger
__all__ = [
    'AUDIT_COMMANDS',
    'DELIVERY_GATE_COMMANDS',
    'DIAGNOSIS_COMMANDS',
    'PLANNING_COMMANDS',
    'SECURITY_COMMANDS',
    'BaseQuickCommand',
    'QuickGuard',
    'build_parser',
    'cmd_agent_template',
    'cmd_arch_rules',
    'cmd_audit_patterns',
    'cmd_biz_chain',
    'cmd_blindspot_scan',
    'cmd_call_chain',
    'cmd_concolic',
    'cmd_coverage_scan',
    'cmd_delivery_gate',
    'cmd_estimate_splits',
    'cmd_fanout',
    'cmd_guard_install',
    'cmd_guard_snapshot',
    'cmd_guard_status',
    'cmd_import_check',
    'cmd_light_diag',
    'cmd_runtime_analysis',
    'cmd_security',
    'cmd_solidify',
    'cmd_split_plan',
    'cmd_stub_scan',
    'diag_call_chain',
    'main',
    'register_cli_audit',
    'register_cli_diagnosis',
    'register_cli_planning',
    'register_cli_security',
    'register_delivery_gate',
]
def diag_call_chain(project_root: str | os.PathLike=DEFAULT_PROJECT_ROOT,
                    source_paths: list[str] | None=None, ctx: Any=None,
                    include_tests: bool | None = None) -> Any:
    if isinstance(project_root, os.PathLike):
        project_root = os.fspath(project_root)
    project_root = validated_warmed_root(project_root)
    builder = CallGraphBuilder(project_root, ctx=ctx,
                               include_tests=include_tests)
    graph = builder.build(source_paths)
    log_call_chain_summary(project_root, graph)
    return graph
@cli_boundary("call-chain", "调用链诊断失败")
def cmd_call_chain(args: argparse.Namespace) -> None:
    project_root = resolve_project_root(args, "call-chain")
    graph = diag_call_chain(
        project_root, getattr(args, "paths", None) or None,
        include_tests=getattr(args, "include_tests", False))
    s = graph.analyses.summary.summary()
    print(f"总函数数: {s.get('total_functions')}  公开函数: {s.get('public_functions')}  "
          f"总调用数: {s.get('total_calls')}  孤立函数: {s.get('orphans')}  断裂点: {s.get('break_points')}")
    break_points = graph.analyses.breakpoints.get_break_points()
    for bp in break_points:
        print(f"  [{str(bp.get('severity', '?')).upper()}] {bp.get('type')}: {str(bp.get('message', ''))[:100]}")
    if getattr(args, "json", False):
        data = {
            "summary": s,
            "break_points": break_points,
            "orphans": [f.name for f in graph.orphans],
            "external_deps": sorted(graph.external_deps),
        }
        emit_json_report(
            data, resolve_report_path(args, "call_chain_report.json"))
@cli_boundary("guard-install", "运行时守卫安装失败")
def cmd_guard_install(args: argparse.Namespace) -> None:
    paths = getattr(args, "paths", None) or None
    skill_ref = getattr(args, "skill", "") or ""
    skill_dir = ""
    if skill_ref:
        skill_dir = resolve_skill_reference(skill_ref) or ""
        if not skill_dir:
            fail_cli("guard-install",
                     f"未找到技能: {skill_ref}（可传技能名、技能根目录或 SKILL.md 路径）")
    guard_install(source_paths=paths, skill_dir=skill_dir or None)
    st = guard_status()
    cov = st.get("coverage") or {}
    if cov.get("started"):
        print("[OK] 运行时守卫已安装（覆盖率采集 + 异常捕获钩子）")
    else:
        print("[OK] 运行时守卫已安装（异常捕获钩子生效）")
        print("[WARN] 覆盖率采集未启动：无可用会话工作空间或 coverage 不可用，"
              "依赖覆盖率的盲区/缺口将不可判定（不伪造 0% 覆盖率）")
    print("  coverage: %s" % ("started" if cov.get("started") else "not started"))
@contextlib.contextmanager
def _human_output(args: argparse.Namespace | None):
    if args is not None and getattr(args, "json", False):
        with contextlib.redirect_stdout(sys.stderr):
            yield
        return
    yield
def _emit_machine_json_report(payload: dict, output: str | None = None) -> None:
    if output:
        with contextlib.redirect_stdout(sys.stderr):
            emit_json_report(payload, output)
    print(json_text(payload))
@cli_boundary("guard-snapshot", "快照保存失败")
def cmd_guard_snapshot(args: argparse.Namespace) -> None:
    saved_locally = guard_snapshot()
    st = guard_status()
    cov = st.get("coverage") or {}
    with _human_output(args):
        if saved_locally:
            if cov.get("started"):
                print("[OK] 覆盖率快照已保存")
            else:
                print("[OK] 运行时守卫状态已保存（覆盖率未启动，无覆盖率快照）")
        elif st.get("installed") is not True:
            print("[WARN] 运行时守卫未安装，本次无快照可保存（请先执行 guard-install）")
            logger.warning("[cli:guard-snapshot] 守卫未安装，快照为无操作")
        elif st.get("live") is False:
            print("[WARN] 守卫进程已退出：仅保留安装记录，本次无新增覆盖率数据")
            logger.warning("[cli:guard-snapshot] 守卫非活动，快照为无操作")
        else:
            print("[WARN] 守卫由其他进程持有，本进程未执行快照；"
                  "请在安装守卫的进程内保存")
            logger.warning("[cli:guard-snapshot] 远端守卫状态不等于本进程快照成功")
        print(f"  快照计数: {cov.get('snapshots', 'N/A')}")
    if getattr(args, "json", False):
        print(json_text(st))
@cli_boundary("guard-status", "状态查询失败")
def cmd_guard_status(args: argparse.Namespace) -> None:
    st = guard_status()
    print(json_text(st))
_RUNTIME_FINDING_PRINT_LIMIT = 20
def _print_runtime_findings(result: dict, *, json_mode: bool = False) -> None:
    raw_findings = result.get("findings")
    findings = [f for f in (raw_findings if isinstance(raw_findings, list) else [])
                if isinstance(f, dict)]
    for finding in findings[:_RUNTIME_FINDING_PRINT_LIMIT]:
        _line = finding.get("line")
        _loc = finding.get("file", "")
        if _line not in (None, "", 0):
            _loc = f"{_loc}:{_line}"
        print(f"  [{finding.get('rule_id', '?')}] {_loc}: "
              f"{str(finding.get('message', finding.get('error', '')))[:100]}")
    if len(findings) > _RUNTIME_FINDING_PRINT_LIMIT:
        remaining = len(findings) - _RUNTIME_FINDING_PRINT_LIMIT
        hint = "见 JSON 报告" if json_mode else "未逐条打印（加 --json 输出完整报告）"
        print(f"  ... 其余 {remaining} 条{hint}")
@cli_boundary("runtime-analysis", "运行时分析失败")
def cmd_runtime_analysis(args: argparse.Namespace) -> None:
    project_root = resolve_project_root(args, "runtime-analysis")
    result = run_full_runtime_analysis(project_root)
    sandbox = to_mapping(result.get("sandbox"))
    leak = to_mapping(result.get("resource_leak"))
    print(f"状态: {result.get('status', '?')}  发现总数: {result.get('findings_count', 0)}")
    print(f"沙箱模拟: {sandbox.get('summary', sandbox.get('findings_count', 'N/A'))}")
    print(f"资源泄漏/异常: {leak.get('summary', leak.get('findings_count', 'N/A'))}")
    _print_runtime_findings(result, json_mode=getattr(args, "json", False))
    if getattr(args, "json", False):
        emit_json_report(
            result, resolve_report_path(args, "runtime_analysis_report.json"))
@cli_boundary("blindspot-scan", "盲区扫描失败")
def cmd_blindspot_scan(args: argparse.Namespace) -> None:
    project_root = resolve_project_root(args, "blindspot-scan")
    whitelist_files = parse_csv_option(getattr(args, "whitelist", None))
    ignore_decorators = parse_csv_option(
        getattr(args, "ignore_decorators", None))
    report = scan_blindspots(
        project_root=project_root,
        source_paths=getattr(args, "paths", None) or None,
        include_code=getattr(args, "code", False),
        output_json=getattr(args, "json_output", None),
        whitelist_files=whitelist_files,
        ignore_decorators=ignore_decorators,
    )
    bs = report.summary()
    print(f"总盲区数: {bs.get('total_blindspots')}  层级: {bs.get('by_level', {})}")
    code_skipped = to_mapping(report.metrics.get("code")).get("skipped_reason")
    if getattr(args, "code", False) and code_skipped:
        print("[WARN] 代码层盲区未执行：未提供运行时覆盖率数据"
              "（先 guard-install 采集覆盖率，或省略 --code）；"
              f"reason={code_skipped}")
    html_output = getattr(args, "html_output", None)
    if html_output:
        try:
            render_blindspot_report_html(report.to_report_data(), html_output)
        except (OSError, TypeError, ValueError) as e:
            fail_cli("blindspot-scan", f"HTML 报告写盘失败: {e}")
        print(f"\n[HTML -> {html_output}]")
    if getattr(args, "json", False):
        json_path = resolve_report_path(args, "blindspot_scan_report.json")
        try:
            report.to_json(json_path)
        except (OSError, TypeError, ValueError) as e:
            fail_cli("blindspot-scan", f"JSON 报告写盘失败: {e}")
        print(f"\n[JSON -> {json_path}]")
@cli_boundary("biz-chain", "业务链诊断失败")
def cmd_biz_chain(args: argparse.Namespace) -> None:
    project_root = resolve_project_root(args, "biz-chain")
    cache = get_warmed_cache(project_root)
    ctx = as_diag_ctx(cache)
    include_tests = getattr(args, "include_tests", False)
    builder = CallGraphBuilder(project_root, ctx=ctx,
                               include_tests=include_tests)
    call_graph = builder.build(getattr(args, "paths", None) or None)
    report = diagnose_business_flows(
        project_root=project_root,
        call_graph=call_graph,
        source_paths=getattr(args, "paths", None) or None,
        max_depth=getattr(args, "depth", DEFAULT_MAX_DEPTH),
        ctx=ctx,
        include_tests=include_tests,
    )
    s = report.summary()
    print(f"入口点: {s.get('entry_points')}  业务链: {s.get('business_chains')}  "
          f"模拟成功: {s.get('simulated_chains')}")
    if s.get("reachability_measured"):
        liveness_pct = s["liveness_rate"] * 100
        reachability_text = (
            f"{s.get('reachable_functions')}/{s.get(FIELD_TOTAL_FUNCTIONS)} "
            f"({liveness_pct:.1f}%)")
        never_reachable_text = str(s.get("never_reachable"))
    else:
        reachability_text = (
            f"未度量（项目函数总数 {s.get(FIELD_TOTAL_FUNCTIONS)}）")
        never_reachable_text = "未度量"
    print(f"可达函数: {reachability_text}  "
          f"不可达函数: {never_reachable_text}")
    if getattr(args, "json", False):
        emit_json_report(
            report.to_report_data(),
            resolve_report_path(args, "biz_chain_report.json"),
        )
def _print_light_diag_report(report: dict) -> None:
    cc = report.get("call_chain") or {}
    print(f"[1/3] 调用链: 函数 {cc.get('total_functions', '-')}  孤立 {cc.get('orphans', '-')}  "
          f"断裂点 {cc.get('break_points', '-')}")
    ap = report.get("antipatterns") or {}
    print(f"[2/3] 反模式: 共 {ap.get('total', '-')} 个（扫描 {ap.get('scanned_files', '-')} 文件）")
    for typ, cnt in (ap.get("top_types") or {}).items():
        print(f"    {typ}: {cnt}")
    quality = report.get("quality") or {}
    weakest = quality.get("weakest_dimensions")
    weak = ("、".join(f"{d.get('name')}({d.get('score')})"
                     for d in weakest if isinstance(d, dict))
            if isinstance(weakest, list) else "")
    print(f"[3/3] 十维评分: 总分 {quality.get('overall_score', '-')}"
          f"（{quality.get('overall_grade', '-')}/A-F）"
          + (f"  最弱维度: {weak}" if weak else ""))
    errors = report.get("errors") or []
    print(f"\n判定: {report.get('verdict')}  状态: {report.get('status')}"
          + (f"  步骤错误: {len(errors)}" if errors else ""))
    if report.get("report_path"):
        print(f"报告已落盘: {report['report_path']}")
def _normalize_light_diag_project(value) -> str:
    if isinstance(value, (list, tuple)):
        if len(value) > 1:
            raise ValueError("light-diag 一次只能诊断一个项目根目录")
        value = value[0] if value else None
    return value or DEFAULT_PROJECT_ROOT
@cli_boundary("light-diag", "轻量诊断失败")
def cmd_light_diag(args: argparse.Namespace) -> int:
    project_root = _normalize_light_diag_project(
        getattr(args, "project", None))
    if not os.path.isdir(project_root):
        fail_cli("light-diag", f"项目目录不存在: {project_root}")
    print(f"轻量诊断中：{project_root}（调用链 → 反模式 → 十维评分）")
    report = run_lightweight_diagnosis(
        project_root, top_files=getattr(args, "top_files", DEFAULT_TOP_FILES))
    if getattr(args, "json", False):
        report["report_path"] = resolve_report_path(
            args, "light_diag_report.json")
        emit_json_report(
            report, resolve_report_path(args, "light_diag_report.json"))
    _print_light_diag_report(report)
    return 1 if (report.get("errors") or report.get("status") in {"partial", "error"}) else 0
def _written_payload_matches(path: str, payload: str) -> bool:
    try:
        with open(path, encoding="utf-8") as f:
            return f.read() == payload
    except (OSError, UnicodeDecodeError) as e:
        log_swallowed(__name__, e,
                      context=f'_written_payload_matches:{type(e).__name__}')
        return False
@cli_boundary("coverage-scan", "覆盖率扫描失败")
def cmd_coverage_scan(args: argparse.Namespace) -> int:
    workers: str | int = args.workers
    if isinstance(workers, str) and workers.isdigit():
        workers = int(workers)
    with contextlib.redirect_stdout(sys.stderr):
        res = scan_test_coverage(
            args.project_dir, tests_dir=args.tests_dir,
            threshold=args.threshold, workers=workers,
            max_workers=args.max_workers, data_dir=args.data_dir,
            coordination=not args.no_coordination,
            force_refresh=args.force_refresh,
            force_parallel=args.force_parallel,
            wait_timeout_s=args.wait_timeout_s,
            cache_max_age_s=args.cache_max_age_s,
            skip_prewarm=args.skip_prewarm, timeout_s=args.timeout_s)
        if res.get("ok"):
            apply_coverage_extras(
                res["data"], gaps_out=args.gaps_out,
                diff_against=args.diff_against,
                project_dir=args.project_dir)
        payload = json_text(res)
        if args.json_out:
            write_coverage_payload(args.json_out, payload)
    if args.json_out and not _written_payload_matches(args.json_out, payload):
        fail_cli("coverage-scan",
                 f"--json-out 未落盘或内容不一致: {args.json_out}", code=2)
    print(payload)
    return 0 if res.get("ok") else 1
_FANOUT_DEFAULTS = FanoutConfig()
@cli_boundary("fanout", "扇出诊断失败")
def cmd_fanout(args: argparse.Namespace) -> int:
    if getattr(args, "rescan", False) and not getattr(args, "verify", False):
        fail_cli("fanout", "--rescan 仅可与 --verify 一起使用", code=2)
    project_root = resolve_project_root(args, "fanout")
    config = FanoutConfig(
        min_severity=args.min_severity,
        seed_limit=args.seed_limit,
        include_tests=not args.exclude_tests,
        min_level=args.min_level,
    )
    if args.gate:
        payload = fanout_residual_gate(project_root)
    elif args.verify:
        payload = verify_fanout_residual(
            project_root, rescan=args.rescan, config=config)
    else:
        _source, _source_path, _round_ts = resolve_fanout_diagnosis_inputs(
            project_root)
        payload = run_fanout_diagnosis(
            project_root, _source, config=config,
            round_start_ts=_round_ts, source_report_path=_source_path)
    if args.html:
        _status = str(payload.get("status") or "")
        if _status and _status != "completed":
            print(f"[WARN] 本轮扇出状态为 {_status}，不发射 HTML"
                  "（避免把上一轮报告当成本轮产物）")
        else:
            _html = emit_fanout_html(
                project_root, renderer=generate_html_report)
            payload["html_status"] = _html.get("status", "")
            payload["html_path"] = _html.get("path", "")
    if args.json_out:
        write_json_artifact(args.json_out, payload, indent=2)
    print(json_text(payload))
    return 0 if normalize_passed(payload.get("passed")) else 1
def _register_fanout(sub) -> None:
    p_fan = sub.add_parser(
        "fanout", help="缺陷扇出诊断（种子签名 + 全库同族位点 + 残留门禁）")
    p_fan.add_argument("project", help="被测技能根目录")
    p_fan.add_argument(
        "--min-severity", default=_FANOUT_DEFAULTS.min_severity,
        help=f"种子严重度门槛（默认 {_FANOUT_DEFAULTS.min_severity}）")
    p_fan.add_argument(
        "--seed-limit", type=int, default=_FANOUT_DEFAULTS.seed_limit,
        help=f"种子上限（默认 {_FANOUT_DEFAULTS.seed_limit}）")
    p_fan.add_argument(
        "--min-level", default=_FANOUT_DEFAULTS.min_level,
        choices=("exact", "variant", "weak"),
        help=f"位点最低命中级别（默认 {_FANOUT_DEFAULTS.min_level}）")
    p_fan.add_argument("--exclude-tests", action="store_true",
                       help="不扫描 tests/ 目录")
    fanout_mode = p_fan.add_mutually_exclusive_group()
    fanout_mode.add_argument("--gate", action="store_true",
                             help="只跑残留门禁（读取最新报告）")
    fanout_mode.add_argument("--verify", action="store_true",
                             help="残留验收：终态 + 治理策略 + 文件完整性")
    p_fan.add_argument("--html", action="store_true",
                       help="同时发射阶段G HTML 报告（htm 归口）")
    p_fan.add_argument("--rescan", action="store_true",
                       help="验收时对同族签名复扫（治疗后再匹配）")
    p_fan.add_argument("--json-out", default=None,
                       help="JSON 报告落盘路径（可选）")
DIAGNOSIS_COMMANDS = {
    "call-chain": cmd_call_chain,
    "blindspot-scan": cmd_blindspot_scan,
    "biz-chain": cmd_biz_chain,
    "runtime-analysis": cmd_runtime_analysis,
    "light-diag": cmd_light_diag,
    "guard-install": cmd_guard_install,
    "guard-snapshot": cmd_guard_snapshot,
    "guard-status": cmd_guard_status,
    "coverage-scan": cmd_coverage_scan,
    "fanout": cmd_fanout,
}
def _add_source_paths_args(parser) -> None:
    parser.add_argument("paths", nargs="*", help="源文件路径")
    parser.add_argument("-p", "--project", default=DEFAULT_PROJECT_ROOT,
                        help="项目根目录")
def _add_json_report_args(parser) -> None:
    parser.add_argument("--json", action="store_true", help="输出 JSON 报告")
    parser.add_argument("-o", "--output", help="JSON 报告输出路径")
def _register_call_chain(sub) -> None:
    p_cc = sub.add_parser("call-chain", help="调用链诊断（构建调用图+断裂点+判定）")
    _add_source_paths_args(p_cc)
    _add_json_report_args(p_cc)
    p_cc.add_argument("--include-tests", action="store_true",
                      help="把 tests 目录计入调用图（默认仅生产代码）")
def _register_blindspot_scan(sub) -> None:
    p_bs = sub.add_parser("blindspot-scan", help="四层盲区扫描（脚本/模块/函数/代码）")
    _add_source_paths_args(p_bs)
    p_bs.add_argument("--code", action="store_true", help="启用代码层盲区（需 coverage）")
    _add_json_report_args(p_bs)
    p_bs.add_argument("--json-output", help="JSON 报告路径（scan_blindspots 直出）")
    p_bs.add_argument("--html-output", help="HTML 报告路径")
    p_bs.add_argument("--whitelist", help="白名单文件路径，逗号分隔（Vulture 风格，命中标识符的盲区被过滤）")
    p_bs.add_argument("--ignore-decorators", help="忽略装饰器名称，逗号分隔（如 property,app.route）")
def _register_biz_chain(sub) -> None:
    p_biz = sub.add_parser("biz-chain", help="业务链运行诊断（入口点→调用链→模拟执行→活性验证）")
    _add_source_paths_args(p_biz)
    p_biz.add_argument("--depth", type=int, default=DEFAULT_MAX_DEPTH,
                       help=f"业务链最大追踪深度（默认 {DEFAULT_MAX_DEPTH}）")
    _add_json_report_args(p_biz)
    p_biz.add_argument("--include-tests", action="store_true",
                       help="把 tests 目录计入业务链（默认仅生产代码）")
def _register_runtime_and_light(sub) -> None:
    p_rt = sub.add_parser("runtime-analysis", help="运行时分析一键入口（沙箱模拟+资源泄漏/异常分析）")
    p_rt.add_argument("project", nargs="?", help="项目/技能根目录（默认当前目录）")
    _add_json_report_args(p_rt)
    p_ld = sub.add_parser("light-diag", help="轻量一键代码诊断（调用链+反模式+十维评分总览）")
    p_ld.add_argument("project", nargs="?", help="项目/技能根目录（默认当前目录）")
    p_ld.add_argument("--top-files", type=int, default=DEFAULT_TOP_FILES,
                      help=f"反模式扫描核心文件数（默认 {DEFAULT_TOP_FILES}）")
    _add_json_report_args(p_ld)
def _register_guard(sub) -> None:
    p_gi = sub.add_parser("guard-install",
                          help="安装运行时守卫（覆盖率采集+异常捕获钩子）")
    p_gi.add_argument("paths", nargs="*", help="监控源文件路径（默认当前目录）")
    p_gi.add_argument("--skill", default="",
                      help="被审计技能根（覆盖率数据落 <工作空间>/Temp/<技能名>/coverage）")
    p_gs = sub.add_parser("guard-snapshot",
                          help="保存运行时守卫覆盖率快照+异常摘要")
    p_gs.add_argument("--json", action="store_true", help="同时输出 JSON 状态")
    sub.add_parser("guard-status",
                  help="查看运行时守卫运行状态")
def _register_coverage_scan(sub) -> None:
    p_cov = sub.add_parser(
        "coverage-scan", help="测试覆盖率实测扫描（xdist 安全采集 + 缺口清单）")
    p_cov.add_argument("project_dir", help="被测项目根目录")
    p_cov.add_argument("--tests-dir", default=None,
                       help="测试目录（默认 project_dir/tests）")
    p_cov.add_argument("--threshold", type=float,
                       default=DEFAULT_COVERAGE_THRESHOLD,
                       help=f"缺口判定线（默认 {DEFAULT_COVERAGE_THRESHOLD}）")
    p_cov.add_argument(
        "--workers", default=DEFAULT_WORKERS,
        help=f"xdist 并行度：auto/整数/0=串行（默认 {DEFAULT_WORKERS}）")
    p_cov.add_argument("--max-workers", type=int, default=None,
                       help="并行度上限钳制（auto 解析为 min(核数,N)）")
    p_cov.add_argument("--no-coordination", action="store_true",
                       help="禁用跨会话协调（指纹缓存/互斥/预算）")
    p_cov.add_argument("--force-refresh", action="store_true",
                       help="忽略缓存命中强制重扫（结果仍登记供复用）")
    p_cov.add_argument("--force-parallel", action="store_true",
                       help="不等待其他会话，直接并行扫（逃生口）")
    p_cov.add_argument("--wait-timeout-s", type=float,
                       default=DEFAULT_WAIT_TIMEOUT_S,
                       help=f"等待其他会话完成的秒数（默认 {DEFAULT_WAIT_TIMEOUT_S:.0f}）")
    p_cov.add_argument("--cache-max-age-s", type=float,
                       default=DEFAULT_CACHE_MAX_AGE_S,
                       help=(f"缓存 TTL 秒（默认 {DEFAULT_CACHE_MAX_AGE_S:.0f}=24h；"
                             "0=每次重扫）"))
    p_cov.add_argument("--data-dir", default=None,
                       help="覆盖率数据目录（默认工作空间 Temp 归口）")
    p_cov.add_argument("--skip-prewarm", action="store_true",
                       help="跳过串行收集预热")
    p_cov.add_argument("--timeout-s", type=int, default=None,
                       help="pytest 主跑超时秒数")
    p_cov.add_argument("--json", action="store_true",
                       help="兼容保留：结果本就始终以 JSON 输出到 stdout，"
                            "该开关不改变输出（落盘用 --json-out）")
    p_cov.add_argument("--json-out", default=None,
                       help="结果 JSON 落盘路径（默认打印）")
    p_cov.add_argument("--gaps-out", default=None,
                       help="缺口上下文 Markdown 导出路径")
    p_cov.add_argument("--diff-against", default=None,
                       help="上一轮 coverage_scan.json 基线路径")
def register_cli_diagnosis(sub) -> None:
    _register_call_chain(sub)
    _register_blindspot_scan(sub)
    _register_biz_chain(sub)
    _register_runtime_and_light(sub)
    _register_guard(sub)
    _register_coverage_scan(sub)
    _register_fanout(sub)
_DEFAULT_FUNC_LINES = 80
_DEFAULT_TEMPLATE_KIND = "cli"
def _fail_concolic_no_targets(path: str) -> NoReturn:
    if os.path.isdir(path):
        fail_cli("concolic",
                 f"目录下没有可探索的 Python 文件（无函数或分支）: {path}")
    if os.path.isfile(path):
        fail_cli("concolic", f"文件中没有可探索的目标函数或路径: {path}")
    fail_cli("concolic", f"文件不存在: {path}")
_CONCOLIC_DIR_MAX_FILES = 5
def _has_concolic_target(filepath: str, func_name: str | None) -> bool:
    source, _fingerprint = read_source_with_fingerprint(filepath, strict=True)
    if source is None:
        return False
    try:
        tree = ast.parse(source)
    except (SyntaxError, ValueError, RecursionError):
        return False
    return any(
        isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and (func_name is None or node.name == func_name)
        for node in walk_nodes(tree)
    )
def _collect_concolic_targets(path: str,
                             func_name: str | None = None) -> list[str]:
    if os.path.isfile(path):
        return [path]
    if not os.path.isdir(path):
        return []
    scored = []
    for filepath in sorted(collect_scan_py_files(path, include_tests=True)):
        score = concolic_file_score(filepath, func_name)
        if score > 0 or _has_concolic_target(filepath, func_name):
            scored.append((score, filepath))
    scored.sort(key=lambda item: (-item[0], os.path.normcase(item[1])))
    return [filepath for _score, filepath in scored[:_CONCOLIC_DIR_MAX_FILES]]
def _explore_concolic_target(filepath: str, path: str, func_name: str | None,
                             executor: SymbolicExecutor, *,
                             multi: bool,
                             json_mode: bool) -> tuple[list[dict], list, int]:
    source = _read_source_or_fail(filepath, "concolic", "读取失败", code=1)
    try:
        results = guided_concolic_explore(
            source, func_name=func_name, symbolic_executor=executor)
    except Exception as e:  # noqa: BLE001
        fail_cli("concolic", f"Concolic 探索失败: {e}")
    if multi and not json_mode:
        print(f"\n[文件] {os.path.relpath(filepath, path)}")
    if not results:
        if not json_mode:
            print("未产出 Concolic 输入（未找到目标函数或无路径可探索）")
        return [], [], 0
    try:
        sink_hits = [r for r in results if r.reached_sink]
        if json_mode:
            rows = [{"file": filepath, **r.to_dict()} for r in results]
        else:
            rows = []
            _render_concolic_results(results, sink_hits)
    except Exception as e:  # noqa: BLE001
        fail_cli("concolic", f"Concolic 结果输出失败: {e}")
    return rows, sink_hits, len(results)
@cli_boundary("concolic", "Concolic 探索命令失败")
def cmd_concolic(args: argparse.Namespace) -> None:
    path = getattr(args, "path", "")
    func_name = getattr(args, "function", None)
    targets = _collect_concolic_targets(path, func_name)
    if not targets:
        _fail_concolic_no_targets(path)
    json_mode = bool(getattr(args, "json", False))
    multi = os.path.isdir(path)
    executor = SymbolicExecutor()
    rows: list[dict] = []
    sink_hits: list = []
    result_count = 0
    for filepath in targets:
        file_rows, file_hits, file_result_count = _explore_concolic_target(
            filepath, path, func_name, executor,
            multi=multi, json_mode=json_mode)
        rows.extend(file_rows)
        sink_hits.extend(file_hits)
        result_count += file_result_count
    if not result_count:
        _fail_concolic_no_targets(path)
    if json_mode:
        print(json_text(rows))
    if sink_hits:
        logger.warning("[cli:concolic] %d 个输入可达危险汇聚点", len(sink_hits))
        sys.exit(1)
def _render_concolic_results(results, sink_hits) -> None:
    print(f"Concolic 探索完成：{len(results)} 个输入，"
          f"其中 {len(sink_hits)} 个可达危险汇聚点")
    for i, r in enumerate(results, 1):
        flag = "[SINK]" if r.reached_sink else "      "
        seed_preview = ", ".join(
            f"{k}={v!r}" for k, v in list(r.values.items())[:4])
        print(f"  {i}. {flag} 约束={r.path_constraints or '-'} "
              f"种子={{{seed_preview}}} 来源={r.seed_source} "
              f"适应度={r.fitness}")
def _print_exploit_summary(exploit_report: dict) -> None:
    if exploit_report.get("status") != "ok":
        return
    exploit_items = exploit_report.get("exploits") or []
    fix_items = exploit_report.get("fixes") or []
    if exploit_items or exploit_report.get("vulnerabilities"):
        print(f"  [利用路径] {len(exploit_items)} 条 / "
              f"[修复建议] {len(fix_items)} 条")
def _security_exploit_addon(args: argparse.Namespace, source: str, fp: str):
    if not getattr(args, "exploit", False):
        return None
    try:
        exploit_report = generate_source_exploit_report(source, filepath=fp)
    except Exception as e:  # noqa: BLE001
        logger.warning("[cli:security] 利用路径报告失败（主扫描保留） %s: %s", fp, e)
        print(f"[WARN] {fp} 利用路径报告失败（安全问题扫描结果保留）: {e}")
        return {"status": "error", "error": str(e)}
    if exploit_report.get("status") != "ok":
        error = exploit_report.get("error") or "未知利用路径分析错误"
        logger.warning(
            "[cli:security] 利用路径报告失败（主扫描保留） %s: %s",
            fp, error)
        print(f"[WARN] {fp} 利用路径报告失败（安全问题扫描结果保留）: {error}")
        return exploit_report
    _print_exploit_summary(exploit_report)
    return exploit_report
def _security_gate_addon(args: argparse.Namespace, source: str, fp: str, issues):
    if not getattr(args, "gate", False):
        return None
    if is_test_file_path(fp):
        return {"ok": True, "block_count": 0, "error_count": 0,
                "warn_count": 0, "message": "测试文件跳过组合门禁",
                "skipped": True}
    try:
        gate = DiagnoseGate()
        findings = [to_gate_finding(iss, fp) for iss in issues]
        g = gate.check_with_security(source, findings, filepath=fp)
        gate_verdict = {
            "ok": g.ok, "block_count": g.block_count,
            "error_count": g.error_count, "warn_count": g.warn_count,
            "message": g.message,
            "issues": [{
                "check_id": issue.check_id,
                "severity": issue.severity.value,
                "message": issue.message,
                "line": issue.line,
                "col": issue.col,
                "suggestion": issue.suggestion,
                "details": issue.details,
            } for issue in (getattr(g, "issues", None) or [])],
        }
        verdict = "通过" if g.ok else "阻断"
        print(f"  [组合门禁] {verdict}: {g.message}")
        return gate_verdict
    except Exception as e:  # noqa: BLE001
        logger.warning("[cli:security] 组合门禁判定失败（主扫描保留） %s: %s", fp, e)
        print(f"[WARN] {fp} 组合门禁判定失败（安全问题扫描结果保留）: {e}")
        return {"ok": False, "error": str(e)}
def _print_security_file_issues(fp: str, result: dict, issues) -> None:
    if not issues:
        return
    print(f"\n{fp}（得分 {result.get('score', '?')}）发现 {len(issues)} 个问题：")
    for i, iss in enumerate(issues, 1):
        print(f"  {i}. [{iss.get('severity', '?')}] {iss.get('category', '?')}"
              f" L{iss.get('line', '?')} sink={iss.get('sink', '?')}"
              f" ({iss.get('cwe_id') or '-'})")
        if iss.get("suggestion"):
            print(f"     建议: {iss['suggestion']}")
def _scan_security_file(
        args: argparse.Namespace, fp: str) -> tuple[dict, int] | None:
    source, _fingerprint = read_source_with_fingerprint(fp, strict=True)
    if source is None:
        logger.warning("[cli:security] 跳过不可读或编码非法文件 %s", fp)
        print(f"[WARN] 跳过 {fp}: 文件不可读或源码编码非法")
        return None
    try:
        result = quick_vulnerability_check(source, filepath=fp)
    except Exception as e:  # noqa: BLE001
        logger.warning("[cli:security] 分析失败跳过 %s: %s", fp, e)
        print(f"[WARN] 跳过 {fp}（分析失败）: {e}")
        return None
    if not isinstance(result, dict):
        logger.warning("[cli:security] 非法扫描结果 %s: 期望 dict，实际 %s",
                       fp, type(result).__name__)
        print(f"[WARN] 跳过 {fp}（非法扫描结果）: "
              f"期望 dict，实际 {type(result).__name__}")
        return None
    if result.get("error"):
        error = result["error"]
        logger.warning("[cli:security] 分析失败跳过 %s: %s", fp, error)
        print(f"[WARN] 跳过 {fp}（分析失败）: {error}")
        return None
    issues = result.get("issues")
    if not isinstance(issues, list):
        logger.warning("[cli:security] 非法扫描结果 %s: issues 期望 list，实际 %s",
                       fp, type(issues).__name__)
        print(f"[WARN] 跳过 {fp}（非法扫描结果）: "
              f"issues 期望 list，实际 {type(issues).__name__}")
        return None
    exploit_report = _security_exploit_addon(args, source, fp)
    gate_verdict = _security_gate_addon(args, source, fp, issues)
    _print_security_file_issues(fp, result, issues)
    file_entry = {"file": fp, "score": result.get("score"),
                  "issues": issues}
    if exploit_report is not None:
        file_entry["exploit_report"] = exploit_report
    if gate_verdict is not None:
        file_entry["gate_verdict"] = gate_verdict
    return file_entry, len(issues)
@cli_boundary("security", "安全扫描命令失败")
def cmd_security(args: argparse.Namespace) -> None:
    path = getattr(args, "path", "")
    if not path or not os.path.exists(path):
        fail_cli("security", f"路径不存在: {path}")
    targets = collect_scan_py_files(path, include_tests=True)
    if not targets:
        fail_cli("security", f"没有可扫描的 Python 文件: {path}", code=1)
    total_issues = 0
    report: dict = {"files": []}
    with _human_output(args):
        for fp in targets:
            scanned = _scan_security_file(args, fp)
            if scanned is None:
                continue
            file_entry, issue_count = scanned
            total_issues += issue_count
            report["files"].append(file_entry)
        report["total_issues"] = total_issues
        gate_blocked = any(
            isinstance(entry.get("gate_verdict"), dict)
            and entry["gate_verdict"].get("ok") is False
            for entry in report["files"])
        report["gate_blocked"] = gate_blocked
        exploit_failed = any(
            isinstance(entry.get("exploit_report"), dict)
            and entry["exploit_report"].get("status") != "ok"
            for entry in report["files"])
        report["exploit_failed"] = exploit_failed
        scanned_count = len(report["files"])
        skipped_count = len(targets) - scanned_count
        report["scanned_count"] = scanned_count
        report["skipped_count"] = skipped_count
        print(f"\n扫描完成：{scanned_count} 个文件，共 {total_issues} 个安全问题"
              + (f"（{skipped_count} 个文件跳过：不可读或分析失败）"
                 if skipped_count else ""))
        if total_issues or gate_blocked or exploit_failed or skipped_count:
            logger.warning("[cli:security] 扫描完成: %d 个文件共 %d 个安全问题, "
                           "门禁阻断=%s, 利用报告失败=%s, 跳过=%d"
                           "（扫描或请求的附加分析不完整不得假绿）",
                           scanned_count, total_issues, gate_blocked,
                           exploit_failed, skipped_count)
    if getattr(args, "json", False):
        _emit_machine_json_report(report, getattr(args, "output", None))
    if total_issues or gate_blocked or exploit_failed or skipped_count:
        sys.exit(1)
def _collect_import_check_quick(project_root: str) -> tuple[dict, bool]:
    summary = quick_check(project_root)
    print(f"[快速模式] 文件 {summary['total_files']} | 高风险裸导入 "
          f"{summary['high_risk_bare_imports']} | 高风险枢纽模块 "
          f"{summary['high_risk_hub_modules']} | 深度错误 "
          f"{summary['depth_errors']} | 传递缺失 "
          f"{summary['transitive_missing']} | 阻断 "
          f"{'是' if summary['blocking'] else '否'}")
    for b in summary["bare_imports"]:
        print(f"  [裸导入] {b['file']}:{b['line']} -> {b['fix']}")
    for h in summary["hub_modules"]:
        print(f"  [枢纽] {h['module']} 被 {h['count']} 个模块引用")
    blocking = bool(summary["blocking"])
    logger.warning("[cli:import-check] 快速模式完成: 文件 %d 高风险裸导入 %d 阻断 %s",
                   summary["total_files"], summary["high_risk_bare_imports"],
                   "是" if blocking else "否")
    return summary, blocking
def _collect_import_check_full(
        project_root: str,
        scanner: ImportSafetyScanner) -> tuple[dict, bool]:
    report = scanner.scan(project_root)
    print_report(report)
    chain_ok, failures = scanner.verify_import_chain(project_root)
    print_import_chain_result(failures)
    payload = import_check_payload(report, chain_ok, failures)
    blocking = bool(report.blocking() or not chain_ok)
    logger.warning("[cli:import-check] 扫描完成: 文件 %d 问题 %d 阻断 %s 导入链 %s",
                   report.total_files, report.total_issues,
                   "是" if report.blocking() else "否",
                   "PASS" if chain_ok else "FAIL")
    return payload, blocking
@cli_boundary("import-check", "导入检查命令失败")
def cmd_import_check(args: argparse.Namespace) -> None:
    project_root = getattr(args, "project_root", "") or DEFAULT_PROJECT_ROOT
    if not os.path.isdir(project_root):
        fail_cli("import-check", f"项目目录不存在: {project_root}", code=2)
    try:
        with _human_output(args):
            if getattr(args, "quick", False):
                payload, blocking = _collect_import_check_quick(project_root)
            else:
                payload, blocking = _collect_import_check_full(
                    project_root, ImportSafetyScanner())
        if getattr(args, "json", False):
            _emit_machine_json_report(payload, getattr(args, "output", None))
    except Exception as e:  # noqa: BLE001
        fail_cli("import-check", f"导入检查失败: {e}", code=2)
    sys.exit(1 if blocking else 0)
SECURITY_COMMANDS = {
    "security": cmd_security,
    "concolic": cmd_concolic,
    "import-check": cmd_import_check,
}
def register_cli_security(sub) -> None:
    p_sec = sub.add_parser("security", help="安全漏洞扫描（污点追踪/注入/XSS/SSTI/反序列化）")
    p_sec.add_argument("path", help="文件或目录路径")
    p_sec.add_argument("--gate", action="store_true", help="附加组合门禁判定（反模式检测+安全发现合并 go/no-go）")
    p_sec.add_argument("--exploit", action="store_true", help="附加源码级漏洞利用路径与修复建议报告")
    _add_json_report_args(p_sec)
    p_con = sub.add_parser("concolic",
                           help="Concolic 导向探索（分支路径约束+具体测试输入生成）")
    p_con.add_argument("path", help="Python 文件路径")
    p_con.add_argument("--function", "-f", default=None,
                       help="目标函数名（默认取第一个函数定义）")
    p_con.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_ic = sub.add_parser("import-check",
                          help="导入安全检查（四维扫描 GF-16/17/18/19 + 导入链完整性验证）")
    p_ic.add_argument("project_root", nargs="?",
                      default=DEFAULT_PROJECT_ROOT,
                      help="项目根目录（默认当前目录）")
    p_ic.add_argument("--quick", action="store_true",
                      help="快速模式（仅报告高风险项）")
    _add_json_report_args(p_ic)
def _render_split_plan(target: str, data: dict) -> None:
    print(f"拆分规划报告: {target}")
    print(f"  可行性评分: {field_of(data, 'score')}/100 | "
          f"策略: {field_of(data, 'strategy', '?')} | "
          f"可拆分: {field_of(data, 'can_split', '?')}")
    print(f"  工作量预估: {field_of(data, 'estimated_effort', '') or '无'}")
    for raw in norm_list(data.get("candidates")):
        c = to_mapping(raw)
        print(f"  [候选] {field_of(c, 'suggested_module', '?')}.py <- "
              f"{len(norm_list(c.get('symbols')))} 符号 "
              f"({field_of(c, 'total_lines')} 行, "
              f"{field_of(c, 'strategy', '?')}): {field_of(c, 'rationale', '')}")
    for risk in norm_list(data.get("import_risks")):
        print(f"  [导入风险] {risk}")
    for risk in norm_list(data.get("circular_risks")):
        print(f"  [循环风险] {risk}")
    for raw in norm_list(data.get("steps")):
        s = to_mapping(raw)
        print(f"  [步骤{field_of(s, 'step_id', '?')}] {field_of(s, 'action', '')}")
    for raw in norm_list(data.get("function_decomposition")):
        s = to_mapping(raw)
        print(f"  [函数分解] {field_of(s, 'function', '?')} "
              f"({field_of(s, 'func_lines')} 行) -> "
              f"{field_of(s, 'suggested_name', '?')} [{field_of(s, 'range', '?')}] "
              f"{field_of(s, 'rationale', '')}")
    print(f"  [回滚] {field_of(data, 'rollback_plan', '')}")
def _read_source_or_fail(path: str, domain: str, label: str,
                        code: int = _DEFAULT_READ_ERROR_CODE) -> str:
    source, _fingerprint = read_source_with_fingerprint(path, strict=True)
    if source is None:
        fail_cli(domain, f"{label}: 无法读取或解码源码文件 {path}", code=code)
    return source
def _read_text_or_fail(path: str, domain: str, label: str,
                       code: int = _DEFAULT_READ_ERROR_CODE) -> str:
    try:
        with open(path, encoding="utf-8-sig") as f:
            return f.read()
    except (OSError, UnicodeDecodeError) as e:
        log_swallowed(__name__, e,
                      context=f'_read_text_or_fail:{type(e).__name__}')
        fail_cli(domain, f"{label}: {e}", code=code)
def cmd_split_plan(args: argparse.Namespace) -> int:
    target = getattr(args, "file", "")
    if not target or not os.path.isfile(target):
        fail_cli("split-plan", f"--file 必须指向存在的文件: {target!r}", code=2)
    func_min = getattr(args, "func_lines", _DEFAULT_FUNC_LINES)
    if func_min < 0:
        fail_cli("split-plan", f"--func-lines 不能为负数: {func_min}", code=2)
    verbose = getattr(args, "verbose", False)
    code = _read_source_or_fail(target, "split-plan", "文件读取失败")
    report = run_cli_action(
        "split-plan", "拆分规划执行异常",
        lambda: plan_split(code, filepath=target),
        code=2, verbose=verbose)
    data = require_dict(
        run_cli_action("split-plan", "拆分规划产物转换失败",
                        report.to_dict, code=2, verbose=verbose),
        "split-plan", "拆分规划产物")
    attach_function_decomposition(data, code, func_min)
    if getattr(args, "json", False):
        emit_json_report(data)
    else:
        _render_split_plan(target, data)
    return 0
def _load_outline_raw(args: argparse.Namespace) -> str:
    outline_raw = getattr(args, "outline", "") or ""
    file_path = getattr(args, "file", "") or ""
    if not outline_raw and not file_path:
        fail_cli("estimate-splits",
                  "需要 --outline '<JSON 数组>' 或 --file outline.json", code=2)
    if file_path:
        return _read_text_or_fail(file_path, "estimate-splits", "大纲文件读取失败")
    return outline_raw
def _outline_json_error(detail) -> str:
    return (f"大纲 JSON 解析失败: {detail}（期望对象数组: "
            "[{'name':..,'func_count':..,'description':..,"
            "'estimated_complexity':..}]）")
def _parse_outline_json(raw: str) -> list:
    try:
        outline = json.loads(raw)
    except (ValueError, TypeError, RecursionError) as e:
        log_swallowed(__name__, e,
                      context=f'_parse_outline_json:{type(e).__name__}')
        fail_cli("estimate-splits", _outline_json_error(e), code=2)
    if not isinstance(outline, list) or not all(
            isinstance(i, dict) for i in outline):
        fail_cli("estimate-splits", _outline_json_error("大纲必须是对象数组"),
                  code=2)
    return outline
def cmd_estimate_splits(args: argparse.Namespace) -> int:
    outline = _parse_outline_json(_load_outline_raw(args))
    est = run_cli_action(
        "estimate-splits", "拆分估算执行异常",
        lambda: estimate_splits(
            outline,
            task_type=getattr(args, "task_type", DEFAULT_TASK_TYPE)),
        code=2, verbose=getattr(args, "verbose", False))
    est_map = to_mapping(est)
    data = {
        "needs_split": field_of(est_map, "needs_split", False),
        "estimated_lines": field_of(est_map, "estimated_lines", 0),
        "recommended_modules": field_of(est_map, "recommended_modules", 0),
        "risk": field_of(est_map, "risk", ""),
        "advice": field_of(est_map, "advice", ""),
        "module_plan": [to_mapping(m)
                        for m in norm_list(est_map.get("module_plan"))],
    }
    if getattr(args, "json", False):
        emit_json_report(data)
    else:
        print(f"拆分预算估算: {len(outline)} 个模块, 预估 {data['estimated_lines']} 行")
        print(f"  风险: {data['risk']} | 建议模块数: {data['recommended_modules']}")
        print(f"  建议: {data['advice']}")
        for m in data["module_plan"]:
            print(f"  [模块] {field_of(m, 'name', '?')}: "
                  f"~{field_of(m, 'est_lines')} 行 "
                  f"({field_of(m, 'func_count')} 函数, "
                  f"{field_of(m, 'complexity', '?')})")
    return 0
def _is_valid_identifier(value: str) -> bool:
    return value.isidentifier() and not keyword.iskeyword(value)
def _require_template_module_name(raw) -> str:
    module_name = (raw or "").strip()
    if not module_name:
        fail_cli("agent-template", "--module 不能为空", code=1)
    if not _is_valid_identifier(module_name):
        fail_cli("agent-template",
                  "--module 必须是合法 Python 标识符（字母/数字/下划线且不以数字开头）: "
                  f"{module_name}", code=1)
    return module_name
def _normalize_template_exports(raw) -> list | None:
    exports = split_csv(raw)
    bad_exports = [item for item in exports if not _is_valid_identifier(item)]
    if bad_exports:
        fail_cli("agent-template",
                  f"--exports 必须是合法 Python 标识符: {', '.join(bad_exports)}",
                  code=1)
    return exports or None
def _normalize_agent_template_inputs(
        args: argparse.Namespace) -> tuple[str, str, str, list | None]:
    module_name = _require_template_module_name(getattr(args, "module", ""))
    description = ((getattr(args, "description", "") or "").strip()
                   or "TODO: 一句话描述模块功能")
    kind = getattr(args, "kind", _DEFAULT_TEMPLATE_KIND) or _DEFAULT_TEMPLATE_KIND
    if kind not in ("cli", "module"):
        fail_cli("agent-template",
                  f"--kind 非法: {kind!r}（可选 cli/module）", code=1)
    raw_exports = getattr(args, "exports", "") or ""
    if kind != "module" and raw_exports.strip():
        fail_cli("agent-template",
                  "--exports 仅适用于 --kind module（cli 模板无显式导出）",
                  code=1)
    exports = (_normalize_template_exports(raw_exports)
               if kind == "module" else None)
    return module_name, description, kind, exports
def cmd_agent_template(args: argparse.Namespace) -> int:
    module_name, description, kind, exports = _normalize_agent_template_inputs(args)
    verbose = getattr(args, "verbose", False)
    if kind == "module":
        content = run_cli_action(
            "agent-template", "模板生成执行异常",
            lambda: generate_agent_module_template(
                module_name, description, exports),
            code=2, verbose=verbose)
    else:
        content = run_cli_action(
            "agent-template", "模板生成执行异常",
            lambda: generate_agent_cli_template(module_name, description),
            code=2, verbose=verbose)
    out_path = getattr(args, "output", "") or f"{module_name}.py"
    if getattr(args, "stdout", False):
        print(content)
        return 0
    out_dir = os.path.dirname(os.path.abspath(out_path))
    if not os.path.isdir(out_dir):
        fail_cli("agent-template", f"输出目录不存在: {out_dir}", code=2,
                  hint="修复建议: 先创建该目录，或用 --output 指定已存在目录下的路径")
    try:
        with guarded_open(out_path, "w", encoding="utf-8",
                          newline="\n") as f:
            f.write(content)
    except (OSError, ValueError) as e:
        log_swallowed(__name__, e,
                      context=f'cmd_agent_template:{type(e).__name__}')
        fail_cli("agent-template", f"模板写盘失败: {e}", code=2)
    print(f"模板已生成: {out_path}（类型={kind}，已内置 CLI 七原则+脚本六原则，可直接通过 check_* 合规检查）")
    return 0
PLANNING_COMMANDS = {
    "split-plan": cmd_split_plan,
    "estimate-splits": cmd_estimate_splits,
    "agent-template": cmd_agent_template,
}
def register_cli_planning(sub) -> None:
    p_sp = sub.add_parser("split-plan",
                          help="拆分规划报告（评分/边界候选/风险/步骤/检查/工作量/回滚，只读不改码）")
    p_sp.add_argument("--file", required=True, help="目标 Python 文件路径")
    p_sp.add_argument("--func-lines", type=int, default=_DEFAULT_FUNC_LINES,
                      dest="func_lines",
                      help="函数级分解的最小函数行数阈值（默认 80，0=关闭）")
    p_sp.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_sp.add_argument("-v", "--verbose", action="store_true", help="详细输出（异常堆栈）")
    p_es = sub.add_parser("estimate-splits",
                          help="生成前拆分预算协商（大纲→行数预估→拆分建议）")
    outline_source = p_es.add_mutually_exclusive_group(required=True)
    outline_source.add_argument(
        "--outline", default="", help="模块大纲 JSON 数组字符串")
    outline_source.add_argument(
        "--file", default="", help="模块大纲 JSON 文件路径")
    p_es.add_argument("--task-type", default=DEFAULT_TASK_TYPE,
                      dest="task_type",
                      help="任务类型（默认 code_write，取 TASK_BUDGETS 预算）")
    p_es.add_argument("--json", action="store_true", help="输出 JSON 报告")
    p_es.add_argument("-v", "--verbose", action="store_true", help="详细输出（异常堆栈）")
    p_at = sub.add_parser("agent-template", help="Agent 友好模板生成（CLI 脚本入口/模块模板，生成即合规）")
    p_at.add_argument("--module", required=True, help="模块名（如 my_tool）")
    p_at.add_argument("--description", default="", help="一句话功能描述")
    p_at.add_argument("--kind", choices=["cli", "module"],
                      default=_DEFAULT_TEMPLATE_KIND,
                      help="模板类型（默认 cli）")
    p_at.add_argument("--exports", default="", help="模块模板显式 __all__ 导出（逗号分隔，仅 module 类型）")
    p_at.add_argument("-v", "--verbose", action="store_true",
                      help="详细输出（异常堆栈）")
    template_output = p_at.add_mutually_exclusive_group()
    template_output.add_argument(
        "-o", "--output", help="输出文件路径（默认 <module>.py）")
    template_output.add_argument(
        "--stdout", action="store_true", help="打印到 stdout 不落盘")
def _emit_solidify_text_or_json(
        args: argparse.Namespace, payload, text: str) -> None:
    output = getattr(args, "output", None)
    if getattr(args, "json", False):
        emit_json_report(payload, output)
        return
    if output:
        try:
            atomic_write_text(
                output, text if text.endswith("\n") else text + "\n",
                tag="SolidifyCLI", newline="\n")
        except (OSError, ValueError) as e:
            log_swallowed(__name__, e,
                          context=f'_emit_solidify_text_or_json:{type(e).__name__}')
            fail_cli("solidify", f"报告写盘失败: {e}", code=2)
    print(text)
def _solidify_list_rules(args: argparse.Namespace) -> None:
    registry = SolidificationRegistry()
    counts = registry.count()
    lines = [f"=== 代码固化规则 ({counts['total']}条) ==="]
    rule_rows = []
    for level, lname in ((1, "静态"), (2, "动态"), (3, "演进")):
        rules = registry.list_rules(level=level)
        if not rules:
            continue
        lines.append(f"--- L{level} {lname}固化 ({len(rules)}条) ---")
        for r in rules:
            status = "启用" if r.enabled else "停用"
            lines.append(f"  [{r.priority}] {status} {r.rule_id}: {r.name}")
            rule_rows.append(r.to_dict())
    payload = {"total": counts["total"], "rules": rule_rows}
    _emit_solidify_text_or_json(args, payload, "\n".join(lines))
def _solidify_analyze_file(solidifier, path: Path, mode):
    require_file(path, "solidify")
    try:
        return solidifier.solidify_file(path, mode=mode)
    except Exception as e:  # noqa: BLE001
        fail_cli("solidify", f"固化分析失败: {e}")
def _format_solidify_point(point: dict) -> str:
    desc = str(point.get("description") or point.get("rule_name") or "")[:60]
    auto_tag = " [可自动修复]" if point.get("auto_fixable") else ""
    return (f"  L{point.get('level', '?')}:{point.get('rule_id', '?')} "
            f"行{point.get('line', '?')} {desc}{auto_tag}")
def _solidify_dry_run(solidifier, path: Path, mode,
                      args: argparse.Namespace) -> None:
    findings = _solidify_analyze_file(solidifier, path, mode)
    if getattr(args, "json", False) or getattr(args, "output", None):
        _emit_solidify_result(findings, args)
        return
    print(f"预览: {path}")
    print(f"待固化点: {len(findings)}")
    for point in findings:
        print(_format_solidify_point(point))
def _emit_solidify_result(findings: list, args: argparse.Namespace,
                          payload=None) -> None:
    if payload is None:
        payload = findings
    if getattr(args, "json", False):
        emit_json_report(payload, getattr(args, "output", None))
        return
    output = getattr(args, "output", None)
    report_path = Path(output) if output else None
    print(SolidificationReport.generate(findings, report_path))
def _solidify_scan_project(solidifier, path: Path, mode, args: argparse.Namespace) -> None:
    require_dir(path, "solidify")
    try:
        result = solidifier.solidify_dir(str(path), mode=mode)
    except Exception as e:  # noqa: BLE001
        fail_cli("solidify", f"目录固化分析失败: {e}")
    findings = result["findings"]
    if not getattr(args, "json", False):
        print(f"扫描文件: {result['files']}  待固化点: "
              f"{result['solidification_points']}")
    _emit_solidify_result(findings, args, result)
def _solidify_generate_rules(path: Path, args: argparse.Namespace) -> None:
    require_dir(path, "solidify")
    py_files = collect_active_py_files(path)
    generator = SolidificationRuleGenerator()
    try:
        suggestions = generator.generate_from_pattern(py_files)
    except Exception as e:  # noqa: BLE001
        fail_cli("solidify", f"规则生成失败: {e}")
    lines = [f"从模式生成的固化规则建议 ({len(suggestions)}条):"]
    for s in suggestions[:20]:
        lines.append(f"  {s.get('rule_id')}: {s.get('file')} ({s.get('count')}处)")
    payload = {"total": len(suggestions), "suggestions": suggestions}
    _emit_solidify_text_or_json(args, payload, "\n".join(lines))
@cli_boundary("solidify", "固化命令失败")
def cmd_solidify(args: argparse.Namespace) -> None:
    mode = resolve_solidify_mode(getattr(args, "mode", DEFAULT_SOLIDIFY_MODE))
    if getattr(args, "list_rules", False):
        _solidify_list_rules(args)
        return
    solidifier = StaticSolidifier()
    if getattr(args, "dry_run", None):
        _solidify_dry_run(solidifier, Path(args.dry_run), mode, args)
        return
    if getattr(args, "file", None):
        _findings = _solidify_analyze_file(solidifier, Path(args.file), mode)
        _emit_solidify_result(_findings, args)
        return
    if getattr(args, "scan_project", None):
        _solidify_scan_project(solidifier, Path(args.scan_project), mode, args)
        return
    if getattr(args, "generate_rules", None):
        _solidify_generate_rules(Path(args.generate_rules), args)
        return
    fail_cli(
        "solidify",
        "参数缺失：请指定 --list-rules / --file / --scan-project / --dry-run / --generate-rules 之一",
        code=2)
def _stub_scan_json_payload(summary: dict) -> dict:
    payload = {"skill_dir": summary["skill_dir"],
               "total_py_files": summary["total_py_files"],
               "total_stubs": summary["total_stubs"],
               "status": summary["status"],
               "categories": summary["categories"]}
    if summary.get("error"):
        payload["error"] = summary["error"]
    return payload
@cli_boundary("stub-scan", "存量盘点命令失败")
def cmd_stub_scan(args: argparse.Namespace) -> int:
    skill_dir = (getattr(args, "skill_dir", None)
                 or os.path.abspath(DEFAULT_PROJECT_ROOT))
    require_dir(Path(skill_dir), "stub-scan")
    try:
        summary = scan_stubs(skill_dir)
    except Exception as e:  # noqa: BLE001
        fail_cli("stub-scan", f"扫描失败: {e}")
    with _human_output(args):
        _print_stub_report(summary)
    if getattr(args, "json", False):
        emit_json_report(_stub_scan_json_payload(summary),
                         getattr(args, "output", None))
    return 1 if (summary.get("error") or summary.get("status") in {"degraded", "error"}) else 0
@cli_boundary("arch-rules", "架构规则查询命令失败")
def cmd_arch_rules(args: argparse.Namespace) -> None:
    try:
        rules = [r.to_dict() for r in get_architecture_rules()]
    except Exception as e:  # noqa: BLE001
        fail_cli("arch-rules", f"架构规则目录查询失败: {e}")
    if getattr(args, "text", False):
        for r in rules:
            print(f"[{r['severity']}] {r['rule_id']} ({r['principle']}): {r['description']}")
            if r.get('suggestion'):
                print(f"    建议: {r['suggestion']}")
    else:
        print(json_text({"count": len(rules), "rules": rules}))
@cli_boundary("audit-patterns", "审计模式检查命令失败")
def cmd_audit_patterns(args: argparse.Namespace) -> None:
    root = getattr(args, "root", "") or os.getcwd()
    try:
        get_warmed_cache(root)
        if getattr(args, "include_tests", False):
            result = quick_audit_pattern_check(root, include_tests=True)
        else:
            result = quick_audit_pattern_check(root)
    except Exception as e:  # noqa: BLE001
        fail_cli("audit-patterns", f"审计模式检查失败: {e}")
    print(json_text(result))
AUDIT_COMMANDS = {
    "solidify": cmd_solidify,
    "stub-scan": cmd_stub_scan,
    "arch-rules": cmd_arch_rules,
    "audit-patterns": cmd_audit_patterns,
}
def register_cli_audit(sub) -> None:
    p_sol = sub.add_parser("solidify", help="固化引擎入口（待固化点分析/规则清单/模式挖掘建议）")
    solidify_action = p_sol.add_mutually_exclusive_group(required=True)
    solidify_action.add_argument(
        "--list-rules", action="store_true", help="列出全部固化规则（按级别分组）")
    solidify_action.add_argument("--file", help="单文件固化分析")
    solidify_action.add_argument("--scan-project", help="目录级批量固化分析")
    solidify_action.add_argument("--dry-run", help="预览单文件待固化点")
    solidify_action.add_argument(
        "--generate-rules", help="从源码重复模式生成固化规则建议")
    p_sol.add_argument("--mode", default=DEFAULT_SOLIDIFY_MODE.value,
                       choices=[mode.value for mode in SolidifyMode],
                       help=("固化模式（SolidifyMode：按模式选择启用的规则类型子集，"
                             f"默认 {DEFAULT_SOLIDIFY_MODE.value}）"))
    p_sol.add_argument("--json", action="store_true", help="输出 JSON 格式")
    p_sol.add_argument("-o", "--output", help="报告输出路径（默认打印）")
    p_stub = sub.add_parser("stub-scan", help="兼容桩/门户文件存量盘点（全目录分类清单）")
    p_stub.add_argument("skill_dir", nargs="?", default=None,
                        help="技能/项目目录路径（默认扫描当前目录）")
    _add_json_report_args(p_stub)
    p_ar = sub.add_parser("arch-rules",
                          help="内置架构规则目录查询（ARCH-* 11 条清单）")
    p_ar.add_argument("--text", action="store_true", help="输出人类可读格式（默认 JSON）")
    p_ap = sub.add_parser("audit-patterns",
                          help="审计模式快速检查（by_detector 统计 + 全部发现）")
    p_ap.add_argument("root", nargs="?", default="", help="目标根目录（默认当前目录）")
    p_ap.add_argument("--include-tests", action="store_true",
                      help="同时扫描 tests/（默认排除，避免测试替身误报）")
def _load_json_object_arg(path: str, label: str) -> dict:
    data = load_json_file("delivery-gate", path, f"{label}不存在",
                          f"{label}加载失败", code=2)
    if not isinstance(data, dict):
        fail_cli("delivery-gate",
                 f"{label}顶层必须是 JSON 对象（字典），"
                 f"实际类型: {type(data).__name__}", code=2)
    return data
def _assemble_gate_inputs(args: argparse.Namespace,
                          project_path: str) -> tuple[dict, Any, dict | None]:
    baseline: dict = {}
    if getattr(args, "baseline", None):
        baseline = _load_json_object_arg(args.baseline, "基线文件")
    qm = None
    if getattr(args, "quality_monitor", None):
        try:
            qm = BatchQualityMonitor(project_path,
                                     baseline_dir=args.quality_monitor)
        except Exception as e:  # noqa: BLE001
            fail_cli("delivery-gate", f"质量监控器构造异常: {e}", code=2)
    fm = None
    if getattr(args, "function_mapping", None):
        fm = _load_json_object_arg(args.function_mapping, "函数映射文件")
    return baseline, qm, fm
@cli_boundary("delivery-gate", "交付门禁命令失败")
def cmd_delivery_gate(args: argparse.Namespace) -> None:
    _t0 = time.monotonic()
    project_path = getattr(args, "project_path", "")
    if not project_path or not os.path.isdir(project_path):
        fail_cli("delivery-gate", f"项目目录不存在: {project_path}", code=2)
    baseline, qm, fm = _assemble_gate_inputs(args, project_path)
    report = run_cli_action(
        "delivery-gate", "交付门禁执行异常", run_full_delivery_gate,
        project_path, baseline,
        quality_monitor=qm, function_mapping=fm,
        override_code=getattr(args, "override_code", "") or "",
        force=bool(getattr(args, "force", False)),
        verbose=getattr(args, "verbose", False), code=2)
    result = format_delivery_ci_output(report)
    _emit_delivery_output(args, result)
    verdict = result.get("verdict", "PENDING")
    passed_gates = result.get("passed_gates", 0)
    failed_gates = result.get("failed_gates", 0)
    passed = verdict == "APPROVED"
    finish_cli_command(
        "delivery-gate", "cmd_delivery_gate", _t0,
        ok=passed, outcome=str(verdict or "UNKNOWN"),
        message=(f"判定: {verdict}（通过 {passed_gates} 道"
                 f"/失败 {failed_gates} 道）"),
        run_fields={"passed_gates": passed_gates,
                    "failed_gates": failed_gates})
def _emit_delivery_output(args: argparse.Namespace, result: dict) -> None:
    output = getattr(args, "output", None)
    if getattr(args, "ci", False):
        _emit_machine_json_report(result, output)
        return
    if output:
        dump_json_report_checked(output, result, "delivery-gate")
    _print_delivery_summary(result)
def _print_delivery_summary(result: dict) -> None:
    print(f"交付门禁判定: {result.get('verdict', 'PENDING')}")
    print(f"通过 {result.get('passed_gates', 0)} 道 "
          f"/ 失败 {result.get('failed_gates', 0)} 道"
          f" / 综合分 {result.get('overall_score', 0.0)}")
    for issue in result.get("blocking_issues", []) or []:
        print(f"  [阻断] {issue}")
def register_delivery_gate(sub) -> None:
    p_dg = sub.add_parser(
        "delivery-gate",
        help="交付前硬门禁（重构交付门禁，CI 退出码 0/1/2）")
    p_dg.add_argument("project_path", help="项目路径")
    p_dg.add_argument("--baseline", "-b", help="基线 JSON 文件路径")
    p_dg.add_argument("--quality-monitor", "-q", help="质量监控器基线目录")
    p_dg.add_argument("--function-mapping", "-m", help="函数映射 JSON 文件路径")
    p_dg.add_argument("--output", "-o", help="输出报告 JSON 文件路径")
    p_dg.add_argument("--ci", action="store_true", help="CI 模式：仅输出 JSON")
    p_dg.add_argument("--override-code", help="紧急覆盖码（SHA256）")
    p_dg.add_argument("--force", action="store_true", help="强制执行（即使覆盖码无效）")
    p_dg.add_argument("-v", "--verbose", action="store_true", help="详细输出（异常堆栈）")
DELIVERY_GATE_COMMANDS = {
    "delivery-gate": cmd_delivery_gate,
}
_ERROR_CATEGORY_UNKNOWN = "未知错误"
_ERROR_CATEGORIES: tuple[tuple[type[BaseException], str], ...] = (
    (ValueError, "参数错误"),
    (FileNotFoundError, "文件未找到"),
    (ImportError, "导入失败"),
    (RuntimeError, "执行错误"),
    (TypeError, "执行错误"),
    (AttributeError, "执行错误"),
    (OSError, "执行错误"),
)
def _error_category(exc: BaseException) -> str:
    for exc_type, category in _ERROR_CATEGORIES:
        if isinstance(exc, exc_type):
            return category
    return _ERROR_CATEGORY_UNKNOWN
@dataclass
class BaseQuickCommand:
    app_name: ClassVar[str] = _PACKAGE_NAME
    command_name: str = ""
    description: str = ""
    arg_name: str | None = "path"
    arg_help: str = "文件或目录路径"
    def run(self, args: argparse.Namespace) -> dict[str, Any]:
        raise NotImplementedError(f"{self.command_name} 必须覆写 run() 方法")
    def self_test(self) -> bool:
        _log.info("%s v%s - %s 自检通过", self.app_name, __version__,
                  self.command_name)
        return True
    def add_arguments(self, parser: argparse.ArgumentParser) -> None:  # jwsgj:suppress dead_stub IA-03 SK-01 C8_dead_code empty_function
        pass  # jwsgj:suppress empty_function
    def execute(self, argv: list | tuple | str | None = None) -> int:
        output_format = _DEFAULT_OUTPUT_FORMAT
        start = time.perf_counter()
        try:
            args = self._parse_args(_normalize_argv(argv))
            output_format = args.output
            if getattr(args, "self_test", False):
                return self._execute_self_test(output_format, start)
            if getattr(args, "version", False):
                _ver_msg = f"{self.app_name} {self.command_name} v{__version__}"
                print(_ver_msg)
                _log.info(_ver_msg)
                return 0
            return self._run_business(args, output_format, start)
        except Exception as e:  # noqa: BLE001
            category = _error_category(e)
            if category == _ERROR_CATEGORY_UNKNOWN:
                _log.warning(MSG_EXCEPTION_BROAD_HANDLER, exc_info=True)
            return self._handle_error(e, start, category, output_format)
    def _execute_self_test(self, output_format: str, start: float) -> int:
        try:
            passed = bool(self.self_test())
        except Exception as e:  # noqa: BLE001
            _log.error("自检失败: %s: %s", type(e).__name__, e, exc_info=True)
            error_result = {
                "ok": False,
                "error": f"自检失败: {e}",
                "error_type": type(e).__name__,
                "error_category": _error_category(e),
                "command": self.command_name,
                "self_test": "failed",
                "duration_sec": round(time.perf_counter() - start, 3),
            }
            self._write_result(error_result, output_format)
            return 1
        result = {
            "ok": passed,
            "command": self.command_name,
            "self_test": "passed" if passed else "failed",
            "duration_sec": round(time.perf_counter() - start, 3),
        }
        if not passed:
            result["error"] = "自检返回失败"
        self._write_result(result, output_format)
        return 0 if passed else 1
    def _run_business(self, args: argparse.Namespace, output_format: str,
                      start: float) -> int:
        result = self.run(args)
        if not isinstance(result, dict):
            raise TypeError(
                f"{self.command_name}.run() 必须返回 dict，"
                f"实际为 {type(result).__name__}")
        result.setdefault("ok", True)
        result.setdefault("command", self.command_name)
        result["duration_sec"] = round(time.perf_counter() - start, 3)
        self._write_result(result, output_format)
        return 0 if normalize_passed(result.get("ok")) else 1
    def _handle_error(self, exc: Exception, start: float, category: str,
                      output_format: str) -> int:
        _log.exception("%s 执行失败: %s", self.command_name, exc)
        error_result = {
            "ok": False,
            "error": str(exc),
            "error_type": type(exc).__name__,
            "error_category": category,
            "command": self.command_name,
            "duration_sec": round(time.perf_counter() - start, 3),
        }
        self._write_result(error_result, output_format)
        return 1
    def _parse_args(self, argv: list | None = None) -> argparse.Namespace:
        parser = argparse.ArgumentParser(
            description=f"{self.app_name} {self.description}",
            formatter_class=argparse.RawDescriptionHelpFormatter,
        )
        self._add_common_args(parser)
        self.add_arguments(parser)
        return parser.parse_args(argv)
    def _add_common_args(self, parser: argparse.ArgumentParser) -> None:
        parser.add_argument(
            "--output", "-o",
            choices=["text", "json"], default=_DEFAULT_OUTPUT_FORMAT,
            help=f"输出格式（默认 {_DEFAULT_OUTPUT_FORMAT}）",
        )
        parser.add_argument(
            "--version", action="store_true",
            help="显示版本号并退出",
        )
        parser.add_argument(
            "--self-test", action="store_true",
            help="自检模式",
        )
        if self.arg_name:
            parser.add_argument(
                self.arg_name, nargs="?", default=None,
                help=self.arg_help,
            )
    def _write_result(self, result: dict[str, Any], output_format: str) -> None:
        if output_format == _DEFAULT_OUTPUT_FORMAT:
            payload = json.dumps(result, ensure_ascii=False, indent=2, default=str)
        else:
            payload = self._format_text_summary(result)
        print(payload)
        _log.info(payload)
    def _format_text_summary(self, result: dict[str, Any]) -> str:
        status = "OK" if normalize_passed(result.get("ok")) else "FAIL"
        summary = f"[{status}] {self.description}"
        for k, v in result.items():
            if k in ("ok", "duration_sec", "name", "command"):
                continue
            if isinstance(v, (list, dict)):
                shown = f"({len(v)} items)"
            elif isinstance(v, str) and len(v) > 120:
                shown = v[:120] + "..."
            else:
                shown = v
            summary += f"\n  {k}: {shown}"
        return summary
@dataclass
class QuickGuard(BaseQuickCommand):
    command_name: str = "quick_guard"
    description: str = "一站式守卫检查"
    arg_name: str | None = "file"
    arg_help: str = "待守卫文件路径"
    def run(self, args: Any) -> dict:
        if not args.file:
            raise ValueError("file 参数不能为空")
        return quick_guard(filepath=args.file)
def _domain_registrars():
    return (
        (_skill_runtime.SKILL_COMMANDS, _skill_runtime.register_cli_skill),
        (DIAGNOSIS_COMMANDS, register_cli_diagnosis),
        (SECURITY_COMMANDS, register_cli_security),
        (AUDIT_COMMANDS, register_cli_audit),
        (INCREMENTAL_REVIEW_COMMANDS, register_incremental_review),
        (DELIVERY_GATE_COMMANDS, register_delivery_gate),
        (REFACTOR_DISCIPLINE_COMMANDS, register_refactor_discipline),
        (CONTRACT_COMMANDS, register_cli_contract),
        (PLANNING_COMMANDS, register_cli_planning),
        (_skill_runtime.MAINTENANCE_COMMANDS, _skill_runtime.register_cli_maintenance),
    )
def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog=_PACKAGE_NAME,
        description=f"{_PACKAGE_NAME} 技能管理统一操作入口",
    )
    sub = parser.add_subparsers(dest="command", required=True)
    for _, register in _domain_registrars():
        register(sub)
    return parser
def _collect_commands() -> dict:
    commands: dict = {}
    for cmds, _ in _domain_registrars():
        commands.update(cmds)
    return commands
def main(argv: list | tuple | str | None = None) -> int:
    parser = build_parser()
    try:
        normalized = _normalize_argv(argv)
    except ValueError as e:
        parser.error(str(e))
    args = parser.parse_args(normalized)
    commands = _collect_commands()
    cmd = commands.get(args.command)
    if cmd is None:
        parser.print_help()
        return 2
    logger.info("[cli] 命令开始: %s", args.command)
    started = time.perf_counter()
    try:
        result = cmd(args)
    except SystemExit as e:
        completed = e.code in (0, None)
        logger.info("[cli] 命令%s(code=%s): %s 耗时 %.2fs",
                    "完成" if completed else "提前退出",
                    e.code, args.command, time.perf_counter() - started)
        raise
    except Exception:
        logger.exception("[cli] 命令未捕获异常: %s", args.command)
        raise
    code = _exit_code_of(result)
    logger.info("[cli] 命令%s: %s 耗时 %.2fs",
                "完成" if code == 0 else "失败", args.command,
                time.perf_counter() - started)
    return code
if __name__ == "__main__":
    logger.info(
        "[ModuleLoad] 文件运行纳入统一日志: CLI 入口运行（python -m jwsgj %s）",
        " ".join(sys.argv[1:]) or "<无子命令>",
        extra={"event": "module_load"},
    )
    if _skill_runtime.deps_gate_needed(sys.argv[1:]):
        _skill_runtime.deps_gate()
    sys.exit(main())

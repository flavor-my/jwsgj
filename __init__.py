from __future__ import annotations  # noqa: I001
import keyword as _keyword
import logging as _logging
import os as _os
_log = _logging.getLogger(__name__)
from .runtime_paths import (  # noqa: I001
    ProjectPathError,
    get_backup_base,
    get_temp_base,
    redirect_host_coverage_data as _redirect_host_coverage,
)
from .runtime_scope import (
    PACKAGE_VERSION as __version__,
    SKIP_DEPS_ENV_VAR as _SKIP_DEPS_ENV_VAR,
)
from . import log_config as _log_config
from .log_config import (
    setup_logging,
)
try:
    _log_config.setup_logging()
except Exception as e:  # noqa: BLE001
    _log.warning("日志配置失败（不阻断包导入）: %s", e, exc_info=True)
try:
    _redirect_host_coverage()
except Exception as _e:  # noqa: BLE001
    _log.warning("宿主采集器落点守卫失败（不阻断导入）: %s", _e)
from .diag_self_check import (  # noqa: I001
    HealthStatus,
    HealthVital,
    ensure_deps as _ensure_deps,
    ensure_tool,
    maint_health_check,
    run_health,
)
def _deps_bootstrap_message(result: object) -> str:
    if not isinstance(result, dict):
        return ("依赖自举返回形态违约（期望 dict，实际 "
                f"{type(result).__name__}）")
    if result.get("status") == "ok":
        return ""
    return str(result.get("message") or "依赖自举失败（未提供失败原因）")
if _os.environ.get(_SKIP_DEPS_ENV_VAR) != "1":
    try:
        _deps_result = _ensure_deps()
    except Exception as _deps_exc:  # noqa: BLE001
        _log.warning("运行时依赖自举失败（包加载继续，功能降级）: %s",
                     _deps_exc, exc_info=True)
    else:
        _deps_message = _deps_bootstrap_message(_deps_result)
        if _deps_message:
            _log.warning("运行时依赖自举未完成（包加载继续，功能降级）: %s",
                         _deps_message)
__all__ = [  # noqa: RUF022
    'AICODER_CODE_REFS',
    'AICODER_CODE_REFS_VERSION',
    'AICODER_DIRECT_CHECKS',
    'AafCtx',
    'ActivationDecision',
    'AnalysisResult',
    'ArchCoexistenceDetector',
    'AutoDisclosureOptimizer',
    'BUG_INTERCEPT_HIGH_FREQ_THRESHOLD',
    'BatchDetector',
    'BigFunctionDecomposer',
    'CODE_REFS',
    'CODE_REFS_VERSION',
    'CalibratedScore',
    'CalibrationProfile',
    'CodeRef',
    'CoexistenceCleaner',
    'CohesionAnalyzer',
    'ConfidenceCalibrator',
    'ConsumerReport',
    'CrossSkillOverlapDetector',
    'DESIGN_EXPECTED_MARKER',
    'DETECTOR_ANCHOR_ALIAS',
    'DETECTOR_POOL_KEY_ALIAS',
    'DIAG4_CODE_REFS',
    'DIAG4_CODE_REFS_VERSION',
    'DIAG4_DIRECT_CHECKS',
    'DIAG_CODE_REFS',
    'DIAG_CODE_REFS_VERSION',
    'DIAG_CORE_CODE_REFS',
    'DIAG_SUPPLEMENT_CODE_REFS',
    'DependencyGraph',
    'ENTRY_POINT_PATTERNS',
    'EVOLUTION_ARTIFACT_KEY_SPEC',
    'EXEMPT_DIRS',
    'EXT_CODE_REFS',
    'EXT_CODE_REFS_VERSION',
    'ExperienceAtom',
    'ExperienceCrystallizer',
    'FANOUT_FORBIDDEN_ACTIONS',
    'FANOUT_GATE_BLOCKED_STAGE',
    'FANOUT_GATE_ENFORCEMENT',
    'FANOUT_GATE_PHASE_BASELINE',
    'FANOUT_GATE_PHASE_PRE_TREATMENT',
    'FANOUT_STAGE_ID',
    'FANOUT_STAGE_LABEL',
    'FANOUT_STRATEGIES',
    'FANOUT_STRATEGY_GOVERNANCE',
    'FANOUT_STRATEGY_LABELS',
    'FEEDBACK_ARTIFACTS',
    'FanoutConfig',
    'FanoutGovernance',
    'FixBackendResult',
    'GUARDS_CODE_REFS',
    'GUARDS_CODE_REFS_VERSION',
    'GrowthDelta',
    'GrowthMonitor',
    'GrowthReport',
    'HTMLReport',
    'HealthStatus',
    'HealthVital',
    'LOGIC_CODE_REFS',
    'LOGIC_CODE_REFS_VERSION',
    'LOGIC_DIRECT_CHECKS',
    'MAIN_CODE_REFS',
    'METH_CODE_REFS',
    'METH_CODE_REFS_VERSION',
    'MatchRecord',
    'NET_ANCHOR_ALIAS',
    'PIPELINE_TRIGGER_KEYWORDS',
    'PipelineGuard',
    'ProjectPathError',
    'QualityDimension',
    'QualityReport',
    'QueryFilter',
    'RD_PREVENTION_CHECKS',
    'REVIEW_FRAMEWORK',
    'RE_CHINESE_CHARS',
    'RefactoringExecutorDispatcher',
    'RefactoringWorkflowGuard',
    'RegressionOutcome',
    'ReportFormatter',
    'ReportSection',
    'STUB_CONSTRAINTS',
    'SafeCleaner',
    'SafetyGate',
    'SecurityAnalyzer',
    'SecurityFindingDeduplicator',
    'SemanticMatchResult',
    'SemanticMatcher',
    'SkillActivationRouter',
    'SkillRoutingInfo',
    'SkillSemanticIndex',
    'TASK_PREFERRED_SERIES',
    'TriggerFeedback',
    'TriggerFeedbackLoop',
    'WRITE_CODE_REFS',
    'WRITE_CODE_REFS_VERSION',
    'WRITE_DIRECT_CHECKS',
    'ZeroConsumerChecker',
    '__version__',
    'aaf_verify_behavior',
    'aaf_verify_diag',
    'aaf_verify_hallucination_precheck',
    'aaf_verify_inline',
    'aaf_verify_patch_precheck',
    'aaf_verify_syntax_safety',
    'aggregate_report',
    'analyze_file',
    'analyze_growth',
    'analyze_log_patterns',
    'analyze_perf_bottlenecks',
    'analyze_session',
    'analyze_test_coverage',
    'apply_ai_fix',
    'apply_ai_fix_batch',
    'apply_approved_adjustment',
    'apply_approved_fix',
    'apply_cleanup_fix',
    'check_locator_scope_integrity',
    'apply_cv_uncertain_verdict',
    'apply_refactored_doc',
    'apply_security_write',
    'artifact_registry',
    'attach_code_refs',
    'audit_log_coverage',
    'auto_crystallize',
    'build_ai_fix_list',
    'build_clean_plan',
    'build_dependency_graph',
    'build_diagnosis_evidence',
    'build_fanout_findings',
    'build_fix_step_out',
    'build_fixed_sources',
    'build_preflight',
    'build_review_out',
    'build_symbol_universe',
    'check_log_quality',
    'check_memory_injection_gate',
    'check_precision_gate',
    'check_stub_constraints_for_content',
    'check_zero_backlog',
    'clear_feedback_history',
    'close_loop_check',
    'collect_diagnostic_defense_signals',
    'collect_html_artifacts',
    'compute_information_density',
    'create_skill_doc',
    'cross_validate_deadcode',
    'deduplicate_security_findings',
    'describe_evolution_artifact_keys',
    'describe_pipeline_field_flow',
    'describe_review_item_keys',
    'describe_verdict_trace_keys',
    'detect_fupan',
    'detect_fupan_execution',
    'detect_new_compat_stubs',
    'detect_risks',
    'detect_skill_overlaps',
    'diag_skill',
    'diag_skill_doc',
    'diag_skill_doc_to_markdown',
    'diag_skill_security',
    'enqueue_arch_coexistence_plans',
    'enqueue_cleanup_plan',
    'enrich_diag_findings',
    'enrich_entry_result',
    'ensure_tool',
    'evaluate_memory_density',
    'evaluate_trigger_feedback',
    'evaluate_zero_leftover',
    'execute_treatment_item_core',
    'extract_code_context',
    'extract_code_context_in_project',
    'extract_rule_candidates',
    'fanout_evolution_signal',
    'fanout_module_counts',
    'fanout_pre_treatment_gate',
    'fanout_residual_gate',
    'fanout_treatment_handoff',
    'fixate_fp_rules',
    'format_impact_report',
    'fp_consume_event_risks',
    'fp_consume_log_growth',
    'generate_html_report',
    'generate_treatment_plan',
    'get_ai_fix_candidates',
    'get_ai_review_verdicts',
    'get_backup_base',
    'get_calibrator',
    'get_code_reference',
    'get_constraints_for_task',
    'get_content_quality_rules',
    'get_coverage_report',
    'get_diagnosis_progress',
    'get_effective_adjustments',
    'get_entry_guard',
    'get_fix_order_for_findings',
    'get_memory_search_queries',
    'get_module_consumers',
    'get_pending_enhancements',
    'get_pipeline_progress',
    'get_pipeline_round_trace',
    'get_pipeline_stage_traces',
    'get_pre_creation_search_queries',
    'get_retrospective_history',
    'get_rule_fallback',
    'get_series_rule_ids',
    'get_size_guard',
    'get_standard_sections',
    'get_stub_constraints',
    'get_temp_base',
    'get_template_stats',
    'get_treatment_progress',
    'get_warmed_cache',
    'ground_code_symbols',
    'guarded_step',
    'inject_code_refs_to_prompt',
    'inject_full_prevention_prompt',
    'list_code_ref_rule_ids',
    'list_diag_series',
    'list_logic_rule_ids',
    'list_pending_ai_reviews',
    'locate_targeted_tests',
    'locate_treatment_item',
    'maint_health_check',
    'mark_enhancement_applied',
    'match_pipeline_trigger',
    'plan_single_fix',
    'preflight_api_check',
    'preflight_diagnostic_check',
    'preflight_symbol_check',
    'prepare_diagnostic_context',
    'preview_targeted_tests',
    'probe_pipeline_trigger',
    'profile_test_performance',
    'query_logs',
    'query_methods_progress',
    'quick_analyze',
    'quick_arch_coexistence_scan',
    'quick_cleanup',
    'quick_coexistence_scan',
    'quick_guard',
    'quick_match_skills',
    'quick_route',
    'recommend_cold_start',
    'reconstruct_pipeline_execution',
    'record_defense_feedback',
    'refactor_skill_doc',
    'register_backlog_soft',
    'register_injection_template',
    'register_rule_candidates',
    'reject_cleanup_plan',
    'render_ai_review_html',
    'render_batch_report_html',
    'render_blindspot_report_html',
    'render_coverage_report_html',
    'render_cv_report_html',
    'render_dependency_report_html',
    'render_diagnosis_report_html',
    'render_file_scan_report_html',
    'render_fupan_report_html',
    'render_health_report_html',
    'render_pipeline_report_html',
    'render_pipeline_summary_html',
    'render_retro_report_html',
    'render_security_report_html',
    'render_treatment_item_html',
    'resolve_code_ref',
    'result_to_b1_findings',
    'run_a3_silent_degrade',
    'run_ai_manual_fix',
    'run_ai_manual_fix_step',
    'run_all_ai_reviews',
    'run_auto_enhance_step',
    'set_ai_review_provider',
    'run_b1_unified_ast_analysis',
    'run_code_feedback_step',
    'run_cv_step',
    'run_deadcode_cleanup',
    'run_diagnosis_step',
    'run_dry_route_step',
    'run_fanout_diagnosis',
    'run_feedback_loop',
    'run_feedback_loop_step',
    'run_fix_backend',
    'run_fupan',
    'run_fupan_step',
    'run_guard',
    'run_guided_creation',
    'run_health',
    'run_health_diag',
    'run_log_driven_evolution',
    'run_next_ai_review',
    'run_next_pipeline_step',
    'run_pipeline_batch',
    'run_pipeline_from_trigger',
    'run_refactor_execution',
    'run_refactor_workflow',
    'run_regression_cv_step',
    'run_retrospective',
    'run_review_step',
    'run_security_analysis',
    'run_stage5_review',
    'run_stage6a_fupan',
    'run_targeted_regression',
    'run_treatment_plan_step',
    'run_treatment_step',
    'scan_boundary_imports',
    'scan_signatures',
    'scan_stubs',
    'scan_unregistered_jinhua_artifacts',
    'scan_unregistered_temp_artifacts',
    'score_dimensions',
    'select_fanout_strategy',
    'setup_logging',
    'should_fupan',
    'suggest_pair_resolution',
    'summarize_defense_feedback',
    'summarize_fanout_strategies',
    'summarize_regression',
    'trigger_feedback_message',
    'validate_review_assessment',
    'validate_section_registry',
    'verify_consumption_chain',
    'verify_fupan_writes',
]
from . import (  # noqa: I001
    build_discover_text_doc,  # noqa: F401
    build_preintervention,  # noqa: F401
    build_skill_md_generate,  # noqa: F401
    build_skill_md_optimize,  # noqa: F401
    build_skill_md_quality,  # noqa: F401
    build_text_document,  # noqa: F401
    build_text_frontmatter,  # noqa: F401
    build_text_scoring,  # noqa: F401
    diag_coverage_scan,  # noqa: F401
    diag_delivery_gate,  # noqa: F401
    diag_dependency_core,  # noqa: F401
    diag_file_scanner,  # noqa: F401
    diag_gate_expr,  # noqa: F401
    diag_gate_expr_flow,  # noqa: F401
    diag_gate_loop,  # noqa: F401
    diag_guard_dirfile,  # noqa: F401
    diag_module_surface,  # noqa: F401
    diag_self_check,  # noqa: F401
    diag_symbol_surface,  # noqa: F401
    diag_ten_dim_scorer,  # noqa: F401
    diag_testing_import_audit,  # noqa: F401
    diag_testing_perf,  # noqa: F401
    diag_testing_perf_metrics,  # noqa: F401
    diag_testing_runtime,  # noqa: F401
    diag_testing_static,  # noqa: F401
    engine_a1_structure,  # noqa: F401
    engine_b2_history,  # noqa: F401
    engine_d_security,  # noqa: F401
    hallucination_prewrite,  # noqa: F401
    preintervention_engines,  # noqa: F401
    refactor_source_rewrite,  # noqa: F401
    skill_doc_structure,  # noqa: F401
    testsuite_coverage_map,  # noqa: F401
    testsuite_registry,  # noqa: F401
)
from . import (
    prevention_refs_main as _prevention_refs_main,
)
from .ai_review_governance import (
    apply_approved_adjustment,
    apply_cv_uncertain_verdict,
    fixate_fp_rules,
    list_pending_ai_reviews,
    run_all_ai_reviews,
    run_next_ai_review,
)
from .ai_review_governance_review import (
    REVIEW_FRAMEWORK,
    validate_review_assessment,
)
from .ai_review_item_channels import (
    describe_review_item_keys,
)
from .build_skill_lifecycle import (
    ExperienceAtom,
    ExperienceCrystallizer,
    auto_crystallize,
)
from .build_skill_md_generate import (
    create_skill_doc,
)
from .cleanup_artifacts import (
    EVOLUTION_ARTIFACT_KEY_SPEC,
    FEEDBACK_ARTIFACTS,
    artifact_registry,
    describe_evolution_artifact_keys,
    scan_unregistered_jinhua_artifacts,
    scan_unregistered_temp_artifacts,
)
from .cleanup_file_hygiene import (
    STUB_CONSTRAINTS,
    analyze_file,
    check_stub_constraints_for_content,
    detect_new_compat_stubs,
    get_stub_constraints,
    scan_stubs,
)
from .cleanup_residue import (
    SafetyGate,
    apply_cleanup_fix,
    check_locator_scope_integrity,
    enqueue_cleanup_plan,
    reject_cleanup_plan,
)
from .code_level_feedback_l2 import (
    get_template_stats,
    register_injection_template,
)
from .coexistence_cleaner import (
    ArchCoexistenceDetector,
    CoexistenceCleaner,
    SafeCleaner,
    enqueue_arch_coexistence_plans,
    quick_arch_coexistence_scan,
    quick_cleanup,
    quick_coexistence_scan,
)
from .diag_coverage_scan import (
    profile_test_performance,
)
from .diag_dependency_core import (
    build_symbol_universe,
)
from .diag_detector_assembly import (
    AICODER_DIRECT_CHECKS,
    DIAG4_DIRECT_CHECKS,
    RD_PREVENTION_CHECKS,
    aaf_verify_diag,
)
from .diag_detectors_registry import (
    preflight_diagnostic_check,
)
from .diag_guard_injection_enforce import (
    get_size_guard,
)
from .diag_log_coverage import (
    audit_log_coverage,
)
from .diag_module_topology import (
    scan_boundary_imports,
)
from .diag_split_gate import (
    aaf_verify_patch_precheck,
    get_entry_guard,
    quick_guard,
)
from .diag_symbol_surface import (
    ground_code_symbols,
    preflight_symbol_check,
)
from .diag_types_vocab import (
    FANOUT_FORBIDDEN_ACTIONS,
    FANOUT_STRATEGIES,
    FANOUT_STRATEGY_GOVERNANCE,
    FANOUT_STRATEGY_LABELS,
    FanoutGovernance,
)
from .diag_zero_backlog_gate import (
    check_memory_injection_gate,
    check_precision_gate,
    check_zero_backlog,
    fanout_residual_gate,
)
from .diag_zero_backlog_ledger import (
    describe_verdict_trace_keys,
    get_ai_review_verdicts,
)
from .engine_a3_silent_degrade import (
    run_a3_silent_degrade,
)
from .engine_b1_cohesion import (
    CohesionAnalyzer,
    result_to_b1_findings,
)
from .engine_b2_history import (
    run_b1_unified_ast_analysis,
)
from .engine_d_security import (
    SecurityAnalyzer,
    run_security_analysis,
)
from .engine_f_deadcode import (
    build_clean_plan,
    build_fixed_sources,
    cross_validate_deadcode,
    run_deadcode_cleanup,
)
from .fanout_governance import (
    FANOUT_GATE_BLOCKED_STAGE,
    FANOUT_GATE_ENFORCEMENT,
    FANOUT_GATE_PHASE_BASELINE,
    FANOUT_GATE_PHASE_PRE_TREATMENT,
    fanout_evolution_signal,
    fanout_pre_treatment_gate,
    run_fanout_diagnosis,
)
from .fanout_report import (
    FANOUT_STAGE_ID,
    FANOUT_STAGE_LABEL,
    FanoutConfig,
    build_fanout_findings,
    fanout_module_counts,
    fanout_treatment_handoff,
    scan_signatures,
    select_fanout_strategy,
    summarize_fanout_strategies,
)
from .feedback_coordinator import (
    apply_approved_fix,
)
from .fix_guide_rule_identity import (
    DependencyGraph,
    build_dependency_graph,
    get_fix_order_for_findings,
)
from .fix_safety_gate import (
    AafCtx,
    RegressionOutcome,
    aaf_verify_behavior,
    aaf_verify_hallucination_precheck,
    aaf_verify_inline,
    aaf_verify_syntax_safety,
    apply_security_write,
)
from .fupan_analyzer import (
    AnalysisResult,
    analyze_session,
    close_loop_check,
    detect_fupan,
    detect_fupan_execution,
    should_fupan,
)
from .fupan_engine import (
    QualityDimension,
    QualityReport,
    detect_risks,
    fp_consume_event_risks,
    fp_consume_log_growth,
    quick_analyze,
    run_fupan,
    run_stage6a_fupan,
    score_dimensions,
    verify_consumption_chain,
    verify_fupan_writes,
)
from .hallucination_prewrite import (
    TASK_PREFERRED_SERIES,
    attach_code_refs,
    get_constraints_for_task,
    inject_code_refs_to_prompt,
    inject_full_prevention_prompt,
)
from .html_render_diag import (
    render_blindspot_report_html,
    render_diagnosis_report_html,
    render_file_scan_report_html,
    render_health_report_html,
    render_security_report_html,
)
from .html_render_pipeline import (
    ReportFormatter,
    collect_html_artifacts,
    format_impact_report,
    generate_html_report,
    render_batch_report_html,
    render_cv_report_html,
    render_pipeline_report_html,
    render_pipeline_summary_html,
)
from .html_render_review import (
    render_ai_review_html,
    render_coverage_report_html,
    render_dependency_report_html,
    render_fupan_report_html,
    render_retro_report_html,
    render_treatment_item_html,
)
from .html_report_primitives import (
    HTMLReport,
    ReportSection,
)
from .log_analysis import (
    QueryFilter,
    analyze_log_patterns,
    analyze_perf_bottlenecks,
    check_log_quality,
    query_logs,
    reconstruct_pipeline_execution,
)
from .log_driven_evolution import (
    GrowthMonitor,
    extract_rule_candidates,
    register_rule_candidates,
    run_log_driven_evolution,
)
from .memory_bridge import (
    compute_information_density,
    evaluate_memory_density,
    get_memory_search_queries,
    get_pre_creation_search_queries,
    prepare_diagnostic_context,
)
from .pipeline_report_assembly import (
    aggregate_report,
    register_backlog_soft,
)
from .pipeline_report_delivery import (
    describe_pipeline_field_flow,
    get_pipeline_round_trace,
    get_pipeline_stage_traces,
)
from .pipeline_round_trace import (
    PipelineGuard,
    get_diagnosis_progress,
    get_pipeline_progress,
    get_treatment_progress,
    guarded_step,
    query_methods_progress,
)
from .pipeline_steps_phases import (
    build_review_out,
    run_ai_manual_fix_step,
    run_auto_enhance_step,
    run_code_feedback_step,
    run_cv_step,
    run_dry_route_step,
    run_feedback_loop_step,
    run_fupan_step,
    run_regression_cv_step,
    run_review_step,
    run_stage5_review,
    run_treatment_plan_step,
    run_treatment_step,
)
from .pipeline_trigger_route import (
    run_diagnosis_step,
    run_next_pipeline_step,
    run_pipeline_batch,
    run_pipeline_from_trigger,
    set_ai_review_provider,
)
from .prevention_diag_extra import (
    DIAG4_CODE_REFS,
    DIAG4_CODE_REFS_VERSION,
    DIAG_SUPPLEMENT_CODE_REFS,
)
from .prevention_diag_refs import DIAG_CORE_CODE_REFS
from .prevention_ext_refs import (
    AICODER_CODE_REFS,
    AICODER_CODE_REFS_VERSION,
    EXT_CODE_REFS,
    EXT_CODE_REFS_VERSION,
)
from .prevention_logic_refs import (
    LOGIC_CODE_REFS,
    LOGIC_CODE_REFS_VERSION,
    LOGIC_DIRECT_CHECKS,
    list_logic_rule_ids,
)
from .prevention_method_refs import (
    METH_CODE_REFS,
    METH_CODE_REFS_VERSION,
)
from .prevention_refs_main import (
    CODE_REFS,
    CODE_REFS_VERSION,
    DETECTOR_ANCHOR_ALIAS,
    DETECTOR_POOL_KEY_ALIAS,
    MAIN_CODE_REFS,
    NET_ANCHOR_ALIAS,
    CodeRef,
    enrich_diag_findings,
    enrich_entry_result,
    get_code_reference,
    list_code_ref_rule_ids,
    preflight_api_check,
    resolve_code_ref,
)
from .prevention_write_checks import (
    WRITE_DIRECT_CHECKS,
)
from .prevention_write_refs import (
    GUARDS_CODE_REFS,
    GUARDS_CODE_REFS_VERSION,
    WRITE_CODE_REFS,
    WRITE_CODE_REFS_VERSION,
)
from .refactor_decompose_actions import BigFunctionDecomposer
from .refactor_post_validation import (
    GrowthDelta,
    GrowthReport,
    analyze_growth,
    run_guard,
)
from .refactor_split_actions import (
    RefactoringExecutorDispatcher,
)
from .retrospective_enhancer import run_retrospective
from .retrospective_evolution import (
    BUG_INTERCEPT_HIGH_FREQ_THRESHOLD,
    clear_feedback_history,
    collect_diagnostic_defense_signals,
    record_defense_feedback,
    summarize_defense_feedback,
)
from .retrospective_ledger import (
    get_pending_enhancements,
    get_retrospective_history,
    mark_enhancement_applied,
)
from .shared_cache import (
    BatchDetector,
    get_warmed_cache,
)
from .skill_audit_rules import (
    SecurityFindingDeduplicator,
    deduplicate_security_findings,
)
from .skill_doc_diagnoser import (
    diag_skill_doc,
    diag_skill_doc_to_markdown,
)
from .skill_doc_refactor_guard import (
    apply_refactored_doc,
    refactor_skill_doc,
)
from .skill_doc_render import (
    validate_section_registry,
)
from .testsuite_coverage_map import (
    analyze_test_coverage,
    get_coverage_report,
)
from .testsuite_registry import get_rule_fallback
from .testsuite_runner import (
    locate_targeted_tests,
    run_targeted_regression,
    summarize_regression,
)
from .treatment_evidence import (
    build_diagnosis_evidence,
    extract_code_context,
    extract_code_context_in_project,
    plan_single_fix,
)
from .treatment_experience import (
    FixBackendResult,
    apply_ai_fix,
    apply_ai_fix_batch,
    build_fix_step_out,
    evaluate_zero_leftover,
    execute_treatment_item_core,
    get_ai_fix_candidates,
    preview_targeted_tests,
    run_ai_manual_fix,
    run_fix_backend,
)
from .treatment_feedback import (
    get_effective_adjustments,
    run_feedback_loop,
)
from .treatment_plan import generate_treatment_plan
from .treatment_state import locate_treatment_item
from .xv_intermediate_store import (
    build_ai_fix_list,
)
_DIAG_REF_OVERLAP = set(DIAG_CORE_CODE_REFS) & set(DIAG_SUPPLEMENT_CODE_REFS)
if _DIAG_REF_OVERLAP:
    _log.warning(
        "诊断代码引用表键冲突（补充域覆盖主域）: %s",
        sorted(_DIAG_REF_OVERLAP)[:10])
DIAG_CODE_REFS: dict = {**DIAG_CORE_CODE_REFS, **DIAG_SUPPLEMENT_CODE_REFS}
DIAG_CODE_REFS_VERSION = "1.3.0"
def list_diag_series() -> dict[str, int]:
    return _prevention_refs_main.series_counts(DIAG_CODE_REFS)
def get_series_rule_ids(series: str) -> list[str]:
    return _prevention_refs_main.series_rule_ids(DIAG_CODE_REFS, series)
from .build_module_topology import (  # noqa: I001
    DESIGN_EXPECTED_MARKER,
    ENTRY_POINT_PATTERNS,
    EXEMPT_DIRS,
    ConsumerReport,
    ZeroConsumerChecker,
    get_module_consumers,
)
from .build_pipeline_checks import diag_skill_security
from .build_preflight import build_preflight, run_guided_creation
from .build_skill_consistency import (
    CrossSkillOverlapDetector,
    SemanticMatcher,
    SemanticMatchResult,
    SkillSemanticIndex,
    detect_skill_overlaps,
    quick_match_skills,
    suggest_pair_resolution,
)
from .build_text_scoring import (
    PIPELINE_TRIGGER_KEYWORDS,
    RE_CHINESE_CHARS,
    get_content_quality_rules,
    get_standard_sections,
    match_pipeline_trigger,
    probe_pipeline_trigger,
)
from .build_trigger_activation import (
    ActivationDecision,
    AutoDisclosureOptimizer,
    CalibratedScore,
    CalibrationProfile,
    ConfidenceCalibrator,
    MatchRecord,
    SkillActivationRouter,
    SkillRoutingInfo,
    TriggerFeedback,
    TriggerFeedbackLoop,
    evaluate_trigger_feedback,
    get_calibrator,
    quick_route,
    recommend_cold_start,
    trigger_feedback_message,
)
from .pipeline_report_assembly import diag_skill, run_health_diag
from .refactor_split_actions import (
    RefactoringWorkflowGuard,
    run_refactor_execution,
    run_refactor_workflow,
)
from .surface_build import _ANCHOR_TABLE_BUILD, _TOP_LEVEL_TABLE_BUILD
from .surface_diag import (
    _ANCHOR_TABLE_DIAG,
    _TOP_LEVEL_TABLE_DIAG,
)
__composition_imports__ = {
    "surface_diag": ("_ANCHOR_TABLE_DIAG", "_TOP_LEVEL_TABLE_DIAG"),
    "surface_build": ("_ANCHOR_TABLE_BUILD", "_TOP_LEVEL_TABLE_BUILD"),
}
def _validate_surface_tables(
        *tables: dict[str, tuple[str, ...]]) -> tuple[int, int]:
    owners: dict[str, str] = {}
    modules: set[str] = set()
    for table in tables:
        if not isinstance(table, dict):
            raise TypeError(
                f"登记表必须是「模块 -> 符号集合」映射，得到 {type(table).__name__}")
        for module, symbols in table.items():
            if not isinstance(module, str) or not module:
                raise TypeError(f"登记表模块键必须是非空字符串: {module!r}")
            if not isinstance(symbols, (tuple, list)):
                raise TypeError(
                    f"登记表 {module!r} 的符号集合必须是元组或列表: "
                    f"{type(symbols).__name__}")
            modules.add(module)
            for symbol in symbols:
                if not isinstance(symbol, str):
                    raise TypeError(
                        f"登记表 {module!r} 含非字符串符号: {symbol!r}")
                if not symbol.isidentifier() or _keyword.iskeyword(symbol):
                    raise ValueError(
                        f"登记表 {module!r} 含非法 Python 标识符或保留关键字: "
                        f"{symbol!r}")
                owner = owners.get(symbol)
                if owner is not None and owner != module:
                    raise ValueError(
                        f"登记表符号重复: {symbol!r} 同时归属 "
                        f"{owner!r} 与 {module!r}")
                owners[symbol] = module
    return len(owners), len(modules)
_log.info(
    "包公开面登记表已加载: %d 个符号 / %d 个模块",
    *_validate_surface_tables(
        _ANCHOR_TABLE_DIAG, _TOP_LEVEL_TABLE_DIAG,
        _ANCHOR_TABLE_BUILD, _TOP_LEVEL_TABLE_BUILD,
    ),
)
_log.info(
    "[ModuleLoad] 文件运行纳入统一日志: 包初始化完成（%d 项导出）",
    len(__all__),
    extra={"event": "module_load"},
)

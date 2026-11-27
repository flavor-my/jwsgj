from __future__ import annotations

import copy
import json
import logging
import math
import os
import shutil
import tempfile
import time
from dataclasses import dataclass, field
from typing import Any

from jwsgj.build_safe_write import get_backup_root, prune_backups
from jwsgj.diag_guard_io import fs_path_text, safe_delete
from jwsgj.diag_guard_state import read_json_artifact
from jwsgj.diag_types_normalize import signal_bool
from jwsgj.html_report_stage_doc import (
    normalize_skill_key,
    read_stage_meta,
    stage_of_file,
)
from jwsgj.log_config import ACTIVE_FILES, get_log_dir
from jwsgj.runtime_paths import (
    BACKUP_SUBDIR_NAME,
    EVOLUTION_AUX_ARTIFACTS,
    EVOLUTION_ROOT_ARTIFACTS,
    EVOLUTION_SCRATCH_DIRNAME,
    EVOLUTION_STATE_SECTIONS,
    append_evolution_events,
    evolution_scratch_dir,
    get_html_report_base,
    get_jinhua_dir,
    get_temp_base,
    get_temp_dir,
    governance_acceptance_path,
    governance_baseline_path,
    governance_decisions_path,
    json_artifact_dir,
    json_root_dir,
    path_scoped_namespace,
    read_evolution_state,
    t5_baseline_path,
    write_evolution_section,
)
from jwsgj.runtime_scope import (
    expand_git_bash_path,
    normalize_skill_dir,
    safe_ns,
)

logger = logging.getLogger(__name__)
logger.info("cleanup_artifacts 产物登记与回收域（登记表 + 未登记对账 + "
            "收尾裁剪 + 日志保留期回收）已加载")
__all__ = [
    "ARTIFACT_BOUNDS",
    "ARTIFACT_SCOPES",
    "ARTIFACT_SPANS",
    "EVOLUTION_ARTIFACT_KEY_SPEC",
    "FEEDBACK_ARTIFACTS",
    "ArtifactSpec",
    "artifact_registry",
    "classify_prune_target",
    "cleanup_old_logs",
    "describe_evolution_artifact_keys",
    "is_unregistered_jinhua_artifact",
    "is_unregistered_jinhua_dir",
    "migrate_legacy_evolution_artifacts",
    "migrate_legacy_report_artifacts",
    "prune_consumed_artifacts",
    "prune_stage_artifacts",
    "run_post_completion_governance",
    "scan_unregistered_jinhua_artifacts",
    "scan_unregistered_jinhua_dirs",
    "scan_unregistered_log_artifacts",
    "scan_unregistered_temp_artifacts",
    "scan_unscoped_jinhua_entries",
]
ARTIFACT_SCOPES = frozenset({"jinhua", "log", "temp", "memory"})
ARTIFACT_SPANS = frozenset({"long", "one_shot", "memory_only"})
ARTIFACT_BOUNDS = frozenset({
    "fixed_name_overwrite", "queue_cap", "rolling_prune", "capped_prune",
    "max_history", "ttl_cleanup", "keyed_state", "size_cap",
    "rolling_rounds", "rolling_sessions", "ring_buffer", "whitelist_prune",
    "cache", "self_prune", "memory_only",
})
@dataclass(frozen=True)
class ArtifactSpec:
    name: str
    scope: str
    span: str
    bound: str
    producer: str
    consumers: tuple
    match: str = "exact"
    path_symbols: tuple = field(default_factory=tuple)
    def __post_init__(self) -> None:
        problems: list[str] = []
        if not isinstance(self.name, str) or not self.name.strip():
            problems.append("name 必须是非空字符串")
        if self.scope not in ARTIFACT_SCOPES:
            problems.append(f"scope 未登记: {self.scope!r}")
        if self.span not in ARTIFACT_SPANS:
            problems.append(f"span 未登记: {self.span!r}")
        if self.bound not in ARTIFACT_BOUNDS:
            problems.append(f"bound 未登记: {self.bound!r}")
        if self.match not in ("exact", "prefix", "suffix", "dir"):
            problems.append(f"match 非法: {self.match!r}")
        if not isinstance(self.consumers, tuple):
            problems.append(
                f"consumers 必须是 tuple，得到 {type(self.consumers).__name__}")
        if not isinstance(self.path_symbols, tuple):
            problems.append(
                f"path_symbols 必须是 tuple，得到 {type(self.path_symbols).__name__}")
        if problems:
            raise ValueError(
                f"产物登记项 {self.name!r} 非法: " + "；".join(problems))
FEEDBACK_ARTIFACTS: tuple = (
    ArtifactSpec(
        "evolution_state.json", "jinhua", "long", "keyed_state",
        "runtime_paths",
        ("feedback_coordinator", "retrospective_enhancer",
         "retrospective_ledger", "treatment_feedback",
         "log_driven_evolution", "code_feedback_thresholds",
         "code_level_feedback_l2", "ai_review_item_plan",
         "pipeline_report_delivery"),
        path_symbols=("evolution_state_path", "read_evolution_section",
                      "write_evolution_section",
                      "update_evolution_section",
                      "EVOLUTION_STATE_SECTIONS")),
    ArtifactSpec(
        "evolution_events.jsonl", "jinhua", "long", "size_cap",
        "runtime_paths",
        ("diag_delivery_integrity_gate", "retrospective_ledger"),
        path_symbols=("evolution_events_path", "append_evolution_event",
                      "append_evolution_events", "load_evolution_events")),
    ArtifactSpec(
        "retrospective_report.json", "jinhua", "long", "fixed_name_overwrite",
        "retrospective_enhancer",
        ("pipeline_report_delivery", "retrospective_ledger",
         "retrospective_evolution"),
        path_symbols=("evolution_report_path",)),
    ArtifactSpec(
        "lifecycle_state", "jinhua", "long", "keyed_state",
        "runtime_paths",
        ("build_skill_lifecycle", "build_skill_merge"),
        match="dir",
        path_symbols=("lifecycle_state_dir", "d4_registry_path",
                      "epoch_anchor_dir")),
    *(
        ArtifactSpec(
            filename, "jinhua", "long", "keyed_state", "runtime_paths",
            ("runtime_paths",),
            path_symbols=(f"{key}_path",))
        for key, filename in (
            ("fp_rules", "fp_rules.json"),
            ("fp_suppression", "fp_suppression.json"),
            ("fp_tracker", "fp_tracker.json"),
            ("fp_tracker_rules", "fp_tracker_rules.json"),
            ("fixer_experiences", "_fixer_experiences.json"),
            ("human_confirmations", "_human_confirmations.json"),
            ("evidence_weights", "evidence_weights.json"),
            ("threshold_history", "rule_threshold_history.json"),
            ("solidify_ssot", "_solidify_ssot.json"),
            ("hallucination_registry", "_hallucination_registry.json"),
            ("consumption_state", "consumption_state.json"),
            ("warning_history", "warning_history.json"),
            ("version_history", "_version_history.json"),
            ("trigger_keywords", "trigger_keywords_custom.json"),
            ("zero_backlog_ledger", "zero_backlog_ledger.jsonl"),
            ("ai_review_verdicts", "ai_review_verdicts.jsonl"),
            ("cv_conclusion_history", "cv_conclusion_history.jsonl"),
        )
    ),
    ArtifactSpec(
        "_mutation_cache", "temp", "one_shot", "cache",
        "diag_testing_mutation_runtime",
        ("diag_testing_mutation_runtime", "diag_testing_mutation"),
        match="dir", path_symbols=("MutationResultCache",)),
    ArtifactSpec(
        "sec_gate_scan_cache", "temp", "one_shot", "cache",
        "diag_detector_assembly",
        ("build_pipeline_checks", "diag_detector_assembly"),
        match="dir", path_symbols=("_gate_scan_cache_path",
                                   "GateScanCache")),
    ArtifactSpec(
        "_sec_gate_scan_cache", "temp", "one_shot", "cache",
        "diag_detector_assembly",
        ("build_pipeline_checks", "diag_detector_assembly"),
        match="dir", path_symbols=("_gate_scan_shared_cache_path",
                                   "GateScanCache")),
    ArtifactSpec(
        "pipeline_stages.jsonl", "temp", "one_shot", "size_cap",
        "xv_intermediate_store", ("xv_intermediate_store",),
        path_symbols=("_stage_trace_path",)),
    ArtifactSpec(
        "active-pipeline.json", "temp", "one_shot", "fixed_name_overwrite",
        "pipeline_round_trace",
        ("pipeline_round_trace", "runtime_paths", "xv_intermediate_store"),
        path_symbols=("PIPELINE_STATE_FILENAME",)),
    ArtifactSpec(
        "fanout_report_latest.json", "temp", "one_shot",
        "fixed_name_overwrite", "fanout_report",
        ("fanout_report", "fanout_governance", "diag_zero_backlog_gate"),
        path_symbols=("fanout_report_path", "load_fanout_report")),
    ArtifactSpec(
        "fanout_report_", "temp", "one_shot", "self_prune",
        "fanout_report",
        ("fanout_report", "fanout_governance", "diag_zero_backlog_gate"),
        match="prefix",
        path_symbols=("fanout_report_path", "load_fanout_report")),
    ArtifactSpec(
        ".filecache.pkl", "temp", "one_shot", "fixed_name_overwrite",
        "diag_testing_source", ("diag_testing_source",)),
    ArtifactSpec(
        "_callgraph_share.json", "temp", "one_shot", "fixed_name_overwrite",
        "shared_cache", ("shared_cache", "diag_blindspot_report"),
        path_symbols=("callgraph_share_path", "load_call_graph_share",
                      "persist_call_graph_share")),
    ArtifactSpec(
        "test_suite_bridge_snapshot.json", "temp", "one_shot",
        "fixed_name_overwrite", "testsuite_eval",
        ("testsuite_eval",), path_symbols=("_SNAPSHOT_FILENAME",)),
    ArtifactSpec(
        "coverage", "temp", "one_shot", "fixed_name_overwrite",
        "diag_runtime_forensics",
        ("engine_e2_mutation", "diag_coverage_scan", "cleanup_residue"),
        match="dir"),
    ArtifactSpec(
        "_review_result.json", "temp", "one_shot", "fixed_name_overwrite",
        "pipeline_round_trace",
        ("pipeline_round_trace", "retrospective_ledger"),
        path_symbols=("_review_result_path", "load_review_result_summary")),
    ArtifactSpec(
        "_g4_verified_index.json", "temp", "one_shot",
        "fixed_name_overwrite", "diag_regression_guard",
        ("diag_regression_guard",)),
    ArtifactSpec(
        "_phase1_tracker.json", "temp", "one_shot",
        "fixed_name_overwrite", "build_full_analysis",
        ("build_full_analysis",)),
    ArtifactSpec(
        "_regression_ctx.json", "temp", "one_shot", "fixed_name_overwrite",
        "xv_intermediate_store", ("xv_intermediate_store",)),
    ArtifactSpec(
        "_treatment_state.json", "temp", "one_shot", "fixed_name_overwrite",
        "treatment_state",
        ("treatment_experience",),
        path_symbols=("get_treatment_state_path", "load_treatment_state",
                      "save_treatment_state")),
    ArtifactSpec(
        "_treatment_fix_plan.json", "temp", "one_shot",
        "fixed_name_overwrite", "treatment_state",
        ("treatment_experience",),
        path_symbols=("treatment_fix_plan_path",
                      "load_treatment_fix_plans",
                      "record_treatment_fix_plan")),
    ArtifactSpec(
        "_cv_uncertain_review.json", "temp", "one_shot",
        "queue_cap", "ai_review_queue",
        ("ai_review_governance",),
        path_symbols=("cv_uncertain_path", "enqueue_cv_uncertain",
                      "MAX_CV_UNCERTAIN_HISTORY")),
    ArtifactSpec(
        ".fix_result.json", "temp", "one_shot", "rolling_prune",
        "treatment_state", ("diag_regression_guard",), match="suffix"),
    ArtifactSpec(
        "treatment_plan_", "temp", "one_shot", "rolling_prune",
        "pipeline_round_trace",
        ("pipeline_report_delivery", "pipeline_round_trace",
         "pipeline_steps_phases"),
        match="prefix"),
    ArtifactSpec(
        "cv_full_report_", "temp", "one_shot", "rolling_prune",
        "xv_intermediate_store",
        ("pipeline_report_delivery", "pipeline_steps_phases", "xv_intermediate_store"),
        match="prefix", path_symbols=("load_cv_report_tolerant",)),
    ArtifactSpec(
        "cv_findex_", "temp", "one_shot", "rolling_prune",
        "xv_intermediate_store", ("xv_intermediate_store",), match="prefix"),
    ArtifactSpec(
        "cv_final_report_", "temp", "one_shot", "rolling_prune",
        "xv_intermediate_store",
        ("pipeline_report_delivery", "pipeline_round_trace", "xv_intermediate_store"),
        match="prefix"),
    ArtifactSpec(
        ".sibling_cache_prune.marker", "temp", "one_shot",
        "fixed_name_overwrite", "shared_cache_store",
        ("shared_cache_store",),
        path_symbols=("_SIBLING_PRUNE_MARKER_NAME",)),
    ArtifactSpec(
        "_ai_fix_plan.json", "temp", "one_shot", "queue_cap",
        "ai_review_item_plan",
        ("ai_review_governance", "ai_review_item_channels"),
        path_symbols=("feedback_plan_path",),),
    ArtifactSpec(
        "_ai_adjustment_plan.json", "temp", "one_shot", "queue_cap",
        "ai_review_item_plan",
        ("ai_review_item_plan", "ai_review_governance"),
        path_symbols=("adjustment_plan_path",)),
    ArtifactSpec(
        "_security_fix_plan.json", "temp", "one_shot", "queue_cap",
        "build_pipeline_checks",
        ("ai_review_item_plan", "ai_review_governance"),
        path_symbols=("MAX_SECURITY_PLANS", "enqueue_plan_items",
                      "resolve_security_plan", "security_plan_path",
                      "load_pending_security_plan")),
    ArtifactSpec(
        "_cleanup_ai_plan.json", "temp", "one_shot", "queue_cap",
        "cleanup_residue", ("cleanup_residue", "coexistence_cleaner"),
        path_symbols=("cleanup_plan_path", "MAX_CLEANUP_PLANS",
                      "read_cleanup_plan")),
    ArtifactSpec(
        "pipeline_archive", "temp", "one_shot", "self_prune",
        "pipeline_round_trace", ("pipeline_round_trace",),
        match="dir",
        path_symbols=("ARCHIVE_DIRNAME", "archive_step_result")),
    ArtifactSpec(
        "htm", "temp", "one_shot", "rolling_prune",
        "html_report_stage_doc",
        ("html_report_primitives",
         "html_render_pipeline", "html_render_diag",
         "html_render_review", "html_report_stage_doc"), match="dir",
        path_symbols=("get_html_report_base",)),
    ArtifactSpec(
        "code_feedback_history", "memory", "memory_only", "memory_only",
        "feedback_coordinator", ("feedback_coordinator",),
        path_symbols=("_LATEST_HISTORY_BY_SKILL", "get_code_feedback_history")),
    ArtifactSpec(
        "fix_route", "memory", "memory_only", "memory_only",
        "pipeline_steps_phases", ("pipeline_steps_phases",),
        path_symbols=("mem_bus_put", "mem_bus_take")),
    ArtifactSpec(
        "jwsgj.log", "log", "long", "size_cap",
        "log_config",
        ("log_analysis",),
        match="prefix", path_symbols=("MAIN_LOG_FILE", "get_log_dir")),
    ArtifactSpec(
        "audit_events.jsonl", "log", "long", "size_cap",
        "log_config", ("log_analysis",), path_symbols=("get_log_dir",)),
    ArtifactSpec(
        "test_runs.jsonl", "log", "long", "size_cap",
        "log_config", ("log_config", "log_analysis", "diag_log_coverage"),
        path_symbols=("TEST_RUNS_FILE", "load_test_runs")),
    ArtifactSpec(
        "development_journal.jsonl", "log", "long", "size_cap",
        "log_config", ("cleanup_artifacts",),
        path_symbols=("ACTIVE_FILES",)),
    ArtifactSpec(
        "trigger_events.jsonl", "log", "long", "size_cap",
        "log_config", ("log_config", "cli_skill_runtime"),
        match="prefix", path_symbols=("get_log_dir",)),
    ArtifactSpec(
        "skill_hotness.jsonl", "log", "long", "capped_prune",
        "build_skill_discovery",
        ("build_skill_discovery",),
        match="prefix",
        path_symbols=("STATE_FILE_SKILL_HOTNESS", "evaluate_skill_hotness",
                      "safe_hotness_section")),
    ArtifactSpec(
        "coverage-coord", "temp", "one_shot", "rolling_prune",
        "diag_coverage_runtime", ("diag_coverage_scan",),
        match="dir", path_symbols=("_coord_root",)),
)
def artifact_registry(registry: tuple | None = None) -> tuple:
    items = FEEDBACK_ARTIFACTS if registry is None else tuple(registry)
    invalid = [type(item).__name__ for item in items
               if not isinstance(item, ArtifactSpec)]
    if invalid:
        raise TypeError(
            f"产物登记表只能包含 ArtifactSpec，得到非法项: {invalid[:3]}")
    return items
def _specs_for_scope(scope: str, registry: tuple | None = None) -> tuple:
    return tuple(s for s in artifact_registry(registry) if s.scope == scope)
def _dir_arg(value: object) -> str:
    try:
        path = fs_path_text(value)
    except (TypeError, ValueError):
        return ""
    return path if path.strip() else ""
EVOLUTION_ARTIFACT_KEY_SPEC: dict[str, dict[str, object]] = {
    "retrospective_report.json": {
        "role": "阶段5/6a 复盘报告（固定名覆盖写，当轮复盘全貌快照）",
        "top_keys": {
            "timestamp": "报告生成时刻（ISO；与留痕双链同名时间键可对齐）",
            "session_id": "复盘会话标识",
            "skill_dir": "目标技能根（归属锚）",
            "round_start_ts": "管线轮次标识（跨链 join 主键，写入侧经\n                            peek_round_start_ts 公开 SSOT 注入（原始值\n                            不归一，与留痕双链同形态）；空串=非管线\n                            轮次上下文的独立复盘，如实缺省）",
            "diagnosis_audit": "诊断阶段审计三环结果（方法覆盖/产出完整性）",
            "cv_audit": "交叉验证阶段审计（规则命中/抑制与不确定分布）",
            "treatment_audit": "治疗阶段审计（执行/成功/回滚/误报终态统计）",
            "scores": "复盘质量评分容器（多维加权）",
            "good_practices": "本轮确认的良好实践清单",
            "issues_found": "复盘发现的问题（反哺增强建议的原料）",
            "enhancement_actions": "反哺增强动作清单（阶段6e AI 审核对象来源）",
            "summary": "复盘摘要文本",
            "enhancement_log": "写入增强日志的操作记录（与 enhancement_log.json 联动）",
            "code_feedback_result": "独立复盘模式的代码级反哺结果（管线模式为 None；阶段6c 另行产出）",
            "rollback_audit": "反馈协调器回滚审计（get_rollback_audit 输出）",
            "memory_operations": "复盘记忆操作清单（记忆桥产出，AI 记忆同步执行项）",
            "quality_gate_result": "复盘质量门禁判定（分项与总体结论）",
            "pdca_tracking": "PDCA 跟踪结果（阶段闭环梳理）",
            "status": "复盘执行状态（completed=三环审计已产出；skipped=输入缺失的降级骨架，不代表本轮复盘结论）",
        },
    },
    "enhancement_log": {
        "role": ("阶段6e 反哺进化建议登记与裁决落盘；落点 "
                 "evolution_state.json 的 enhancement_log 节"
                 "（顶层 {entries, sessions} 两层容器）"),
        "top_keys": {
            "entries": "增强建议记录列表（本轮+历史，审核与历史裁决基线消费）",
            "sessions": "会话聚合元信息",
        },
        "entry_keys": {
            "target_id": "增强目标标识（审核定位主键）",
            "action_type": "动作类型（tweak_threshold/add_rule/update_description 等）",
            "description": "建议描述",
            "expected_impact": "预期影响说明",
            "suggested_value": "建议值（统一 FIELD_SUGGESTED_VALUE 键面）",
            "status": "Record 状态（pending/applied/rejected；裁决回填落盘）",
            "phase": "来源管线相位（阶段6b/6c 等）",
            "source": "来源域标识",
            "rule_id": "关联规则号（历史 FP 率/裁决基线关联键）",
            "confidence": "建议置信度", "fp_count": "关联误报计数",
            "fp_pattern": "误报形态说明", "fp_rate": "关联误报率",
            "diagnosis_context": "溯源层1：诊断上下文",
            "treatment_context": "溯源层2：治疗上下文",
            "retrospective_context": "溯源层3：复盘上下文（四层溯源航迹成员）",
            "round_start_ts": "管线轮次标识（跨链 join 主键；全部写路径\n                            统一补齐非替代回填：append_pending_enhancements\n                            SSOT 写入口 / 复盘建议持久化\n                            _persist_review_enhancements / 治疗反哺桥接\n                            retrospective_enhancer._prov_base 三处同源\n                            peek_round_start_ts 注入，条目自带真值不改写；\n                            空串=非轮次上下文，历史遗留条目缺省=归属\n                            不可考，读侧不得臆造回填）",
            "timestamp": "记录生成时刻", "modified_at": "裁决回填时刻",
            "target": "作用于的读者可述目标", "target_type": "目标类型",
        },
    },
    "feedback_history": {
        "role": ("反哺历史权重基线（方法阈值/CV规则权重/修复器需求的跨轮演化）；"
                 "落点 evolution_state.json 的 feedback_history 节"),
        "top_keys": {
            "version": "结构版本号",
            "method_thresholds": "方法阈值历史（L1 反哺调节生效面）",
            "cv_rule_weights": "CV 规则权重历史（L3 反哺调节生效面）",
            "fixer_needs": "修复器需求记录",
            "session_count": "累计会话数",
            "sessions": "逐会话反哺摘要列表（session 级键面：timestamp/\n                       round_start_ts 轮次锚/outcome_summary/feedback_count/\n                       applied_count；轮次锚由 treatment_feedback\n                       写入，空串=非轮次上下文）",
        },
    },
    "cv_conclusion_history": {
        "role": ("CV 结论跨轮历史（振荡检测输入；每行一轮）；落点 "
                 "evolution_state.json 的 cv_conclusion_history 节"),
        "top_keys": {
            "ts": "本轮落盘时刻（ISO，历史兼容键）",
            "timestamp": "统一时间键（写入侧与 ts 同源同值 ISO——"
                        "全链同名时间对齐键，读侧缺失回退 ts，不臆造）",
            "conclusions": "{locator: conclusion} 全图快照",
            "round_start_ts": "管线轮次标识（与 stages/verdicts 双链"
                            "按轮次 join 的对齐锚，旧条目缺省=归属不可考）",
        },
    },
    "zero_backlog_ledger": {
        "role": ("归零门禁台账（追加式事件流，rolling_rounds 保留最近轮次窗口）；"
                 "落点 evolution_state.json 的 zero_backlog_ledger 节"),
        "top_keys": {
            "event": "事件类型（round_open 轮次锚 / finding_seen 发现登记 / "
                    "finding_resolved 终态处置回填）",
            "ts": "事件时刻（Unix 秒浮点，历史兼容键）",
            "at": "事件时刻（人类可读文本，历史兼容键）",
            "timestamp": "统一时间键（ISO；历史事件缺省读侧"
                        "不得臆造回填，时序对齐仅消费确实携键事件）",
            "round_start_ts": "管线轮次标识（跨链 join 主键）",
            "finding_id": "发现终态标识（seen/resolved 两事件型共有）",
            "severity": "finding_seen 严重度档位", "domain": "A-G 七域归属",
            "rule_id": "finding_seen 命中规则号（与 CV finding/治疗项/裁决 "
                       "留痕同词 join 键）",
            "file": "finding_seen 目标文件路径（与 CV finding 同词）",
            "line": "finding_seen 目标行号",
            "locator": "finding_seen 定位子（CV 报告 findings_index 定位键）",
            "message": "finding_seen 问题描述（截前 200 字符）",
            "conclusion": "finding_seen CV 结论（confirmed/likely/uncertain 等）",
            "confidence": "finding_seen 调整后置信度（adjusted_confidence）",
            "sources": "finding_seen 独立来源清单（多源确认证据）",
            "resolution": "finding_resolved 终态词（TERMINAL_RESOLUTIONS）",
            "rationale": "处置理由（可审计，≥10 字符）", "actor": "处置主体",
        },
    },
    "finding_closure": {
        "role": ("日志驱动进化 finding 销项记录；落点 evolution_state.json 的 "
                 "finding_closure 节（键为 finding_id；TTL 30 天 + 容量 2000 条"
                 "按 resolved_at 最旧淘汰）"),
        "top_keys": {
            "resolved_at": "销项时刻（ISO，读侧 SSOT——TTL/淘汰/升级判定消费）",
            "timestamp": "统一时间键（与 resolved_at 同源同值；"
                        "补齐非替代）",
            "round_start_ts": "管线轮次标识（peek_round_start_ts "
                            "SSOT 原始值；历史记录缺省=归属不可考）",
            "skill_dir": "技能根归属锚",
            "resolution": "销项原因", "severity": "销项时严重度档位（可选键）",
        },
    },
    "growth_history": {
        "role": ("技能规模成长趋势快照；落点 evolution_state.json 的 "
                 "growth_history 节（每轮复盘追加一条；max_history 滚动）"),
        "top_keys": {
            "ok": "采集是否成功", "engine": "GrowthMonitor",
            "project_path": "监控基准路径（用户传参原形态）",
            "skill_dir": "技能根归属锚（abspath 归一绝对形态）",
            "round_start_ts": "管线轮次标识（历史快照缺省="
                            "归属不可考）",
            "py_files": "Python 文件数", "total_lines": "总行数",
            "avg_lines_per_file": "平均文件行数",
            "timestamp": "快照时刻（ISO）",
        },
    },
    "_cross_chain_join_anchors": {
        "role": "跨链对齐统一词汇（非产物，join 口径声明）",
        "top_keys": {
            "round_start_ts": "轮次标识：pipeline_stages.jsonl/ai_review_verdicts.jsonl/"
                            "cv_conclusion_history.jsonl/zero_backlog_ledger.jsonl 四事件流 "
                            "+ retrospective_report.json/enhancement_log.json/"
                            "feedback_history.json(sessions)/log_finding_closure.json/"
                            "_growth_history.json 反哺进化"
                            "产物全链共有的对齐主键（写入侧统一经 peek_round_start_ts "
                            "公开 SSOT 注入，原始值不归一与留痕双链同形态；历史遗留条目"
                            "缺省=归属不可考，读侧不得臆造回填）",
            "timestamp": "同名时间统一消费键：双链 + 复盘报告/增强条目/CV 结论历史/"
                        "归零台账/销项记录/成长快照（各产物写入侧补齐；"
                        "旁路历史键 ts/at/resolved_at 保留写入向后兼容，补齐非替代；"
                        "stage 链为 17 位毫秒戳形态、其余 ISO 形态，按轮次分组后"
                        "组内时序对齐）",
            "skill_dir": "归属锚：阶段与裁决留痕顶层 skill_dir（与"
                        "file_path_abs 文件级定位互补）、复盘报告、成长快照/"
                        "销项记录共有",
        },
    },
}
def describe_evolution_artifact_keys() -> dict:
    return copy.deepcopy(EVOLUTION_ARTIFACT_KEY_SPEC)
_PRUNE_PLAN = (
    ("cv",         "reports",     "stale_cv_reports"),
    ("cv_full",    "reports",     "stale_cv_full_reports"),
    ("cv_findex",  "reports",     "stale_cv_findex"),
    ("cv_md",      "reports",     "stale_cv_md_reports"),
    ("plan",       "reports",     "stale_plans"),
    ("fix",        "fix_results", "fix_results"),
    ("aifix_bak",  "none",        "aifix_backups"),
    ("f2_mutbak",  "reports",     "f2_mutbak_dumps"),
)
_PRUNE_GROUP_KEYS = tuple(_key for _key, _keep_src, _group in _PRUNE_PLAN)
_PRUNE_JSON_PREFIXES = (("cv_final_report_", "cv"),
                        ("cv_full_report_", "cv_full"),
                        ("cv_findex_", "cv_findex"),
                        ("treatment_plan_", "plan"))
_PRUNE_JSON_FIX_SUFFIXES = (".fix_result.json", ".autofix.json")
_AIFIX_BACKUP_PREFIX = "aifix_bak_"
_PRUNE_FILE_RULES = (
    (_AIFIX_BACKUP_PREFIX, "", "aifix_bak"),
    ("f2_mutbak_", ".py", "f2_mutbak"),
    ("cv_report_", ".md", "cv_md"),
)
def _classify_json_prune_target(fn: str) -> str | None:
    folded = fn.lower()
    for prefix, key in _PRUNE_JSON_PREFIXES:
        if folded.startswith(prefix):
            return key
    return "fix" if folded.endswith(_PRUNE_JSON_FIX_SUFFIXES) else None
def classify_prune_target(fn: str) -> str | None:
    name = fs_path_text(fn)
    if not name:
        return None
    folded = os.path.basename(name).lower()
    for prefix, suffix, key in _PRUNE_FILE_RULES:
        if folded.startswith(prefix) and folded.endswith(suffix):
            return key
    if folded.endswith(".json"):
        return _classify_json_prune_target(folded)
    return None
def _is_round_protected(path: str, protect_ts: float) -> bool:
    if protect_ts <= 0:
        return False
    try:
        return os.path.getmtime(path) >= protect_ts
    except OSError as e:
        logger.debug("文件状态探测失败（跳过）: %s: %s", path, e)
        return True
def _prune_artifact_group(
    paths: list,
    keep: int,
    group: str,
    protect_ts: float,
    summary: dict,
) -> None:
    summary["kept"][group] = summary["kept"].get(group, 0) + len(paths)
    if len(paths) <= keep:
        return
    try:
        paths.sort(key=lambda p: (os.path.getmtime(p), os.path.normcase(p)),
                   reverse=True)
    except OSError:
        logger.debug("[PruneConsumed] %s mtime 读取失败，整组保留", group)
        return
    _deleted = 0
    for p in paths[keep:]:
        if _is_round_protected(p, protect_ts):
            continue
        if safe_delete(p):
            summary["deleted"] += 1
            summary["groups"][group] = summary["groups"].get(group, 0) + 1
            _deleted += 1
        else:
            logger.debug("[PruneConsumed] 回收站删除未成功(保留): %s", p)
    summary["kept"][group] -= _deleted
def _collect_temp_grouped_paths(temp_dir: str) -> dict | None:
    paths: dict = {key: [] for key in _PRUNE_GROUP_KEYS}
    try:
        for fn in os.listdir(temp_dir):
            key = classify_prune_target(fn)
            path = os.path.join(temp_dir, fn)
            if key is not None and os.path.isfile(path):
                paths[key].append(path)
    except OSError:
        logger.debug("[PruneConsumed] Temp 列目录失败(整轮跳过，含 HTML 组)",
                     exc_info=True)
        return None
    return paths
def _listdir_join(directory: str, accept, label: str) -> list | None:
    if not os.path.isdir(directory):
        return []
    try:
        return [os.path.join(directory, fn)
                for fn in sorted(os.listdir(directory)) if accept(fn)]
    except OSError as e:
        logger.warning("[PruneConsumed] %s 列目录失败: %s", label, e)
        return None
def _collect_backup_group_paths(temp_dir: str) -> list:
    paths = _listdir_join(
        os.path.join(temp_dir, BACKUP_SUBDIR_NAME),
        lambda fn: fn.lower().startswith(_AIFIX_BACKUP_PREFIX),
        "备份子目录")
    return paths if paths is not None else []
def _html_owned_by(path: str, skill_dir: str) -> bool:
    owner = read_stage_meta(path).get("skill", "")
    if not owner:
        return False
    return normalize_skill_key(owner) == normalize_skill_key(skill_dir)
def _collect_html_paths(skill_dir: str = "") -> list | None:
    try:
        html_dir = get_html_report_base()
    except (RuntimeError, ValueError) as _he:
        logger.debug("[PruneConsumed] htm 落点解析失败(跳过HTML裁剪): %s", _he)
        return []
    if not html_dir:
        return []
    listed = _listdir_join(
        html_dir, lambda fn: fn.lower().endswith(".html"), "htm")
    if listed is None:
        return None
    paths = [p for p in listed if os.path.isfile(p)]
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        return paths
    return [p for p in paths if _html_owned_by(p, skill_dir)]
def _stage_json_dir(skill_dir: str) -> str:
    try:
        return json_root_dir(skill_dir)
    except (RuntimeError, ValueError) as exc:
        logger.debug("[StagePairs] zhenduan 落点解析失败: %s", exc)
        return ""
def _stage_companion_path(html_path: str, json_dir: str) -> str:
    if not json_dir:
        return ""
    stem = os.path.splitext(os.path.basename(html_path))[0]
    return os.path.join(json_dir, stem + ".json")
def _pair_mtime(unit: dict) -> float:
    values = []
    for key in ("html", "json"):
        path = unit.get(key) or ""
        if path:
            try:
                values.append(os.path.getmtime(path))
            except OSError:
                continue
    return max(values) if values else 0.0
def _restore_staged_paths(moved: list[tuple[str, str]]) -> bool:
    restored = True
    for staged, original in reversed(moved):
        try:
            if os.path.lexists(original):
                raise FileExistsError(f"回滚目标已存在: {original}")
            os.makedirs(os.path.dirname(original), exist_ok=True)
            shutil.move(staged, original)
        except OSError as exc:
            restored = False
            logger.error("[StagePairs] 回滚 %s -> %s 失败: %s",
                         staged, original, exc)
    return restored
def _discard_empty_dir(path: str) -> None:
    try:
        os.rmdir(path)
    except OSError:
        logger.debug("[StagePairs] 暂存目录非空或不可移除（保留）: %s", path)
def _recycle_stage_unit(skill_dir: str, html_path: str, json_path: str) -> bool:
    paths = [path for path in (html_path, json_path)
             if path and os.path.isfile(path)]
    if len(paths) < 2:
        return not paths or safe_delete(paths[0])
    try:
        temp_dir = get_temp_dir(skill_dir)
        os.makedirs(temp_dir, exist_ok=True)
        staging = tempfile.mkdtemp(prefix=".stage_pair_prune_", dir=temp_dir)
    except (OSError, RuntimeError, ValueError) as exc:
        logger.warning("[StagePairs] 配对暂存目录创建失败（整对保留）: %s", exc)
        return False
    moved: list[tuple[str, str]] = []
    try:
        for original in paths:
            staged = os.path.join(staging, os.path.basename(original))
            shutil.move(original, staged)
            moved.append((staged, original))
    except OSError as exc:
        logger.warning("[StagePairs] 配对暂存失败（回滚）: %s", exc)
        _restore_staged_paths(moved)
        _discard_empty_dir(staging)
        return False
    if safe_delete(staging):
        return True
    logger.warning("[StagePairs] 配对回收失败（回滚）: %s", staging)
    _restore_staged_paths(moved)
    _discard_empty_dir(staging)
    return False
def _stage_json_skill_key(path: str) -> str:
    try:
        with open(path, encoding="utf-8-sig") as handle:
            payload = json.load(handle)
    except (OSError, ValueError, RecursionError) as exc:
        logger.debug("[StagePairs] 配套 JSON 归属读取失败（按无主处理）: %s: %s",
                     path, exc)
        return ""
    if not isinstance(payload, dict):
        return ""
    owner = payload.get("skill_dir")
    if not isinstance(owner, str) or not owner.strip():
        return ""
    return normalize_skill_key(owner)
def _pair_sort_key(unit: dict) -> tuple[float, str]:
    path = unit.get("html") or unit.get("json") or ""
    return (_pair_mtime(unit), os.path.normcase(os.path.basename(path)))
def _prune_stage_pairs(skill_dir: str, keep: int, protect_ts: float,
                       summary: dict) -> None:
    html_paths = _collect_html_paths(skill_dir)
    if html_paths is None:
        logger.warning("[StagePairs] HTML 目录不可枚举（本轮整组保留）")
        return
    json_dir = _stage_json_dir(skill_dir)
    if not json_dir:
        logger.warning("[StagePairs] 配套 JSON 落点不可解析（本轮整组保留）")
        return
    target_key = normalize_skill_key(skill_dir)
    all_html_names: set[str] = set()
    try:
        html_dir = get_html_report_base()
        if os.path.isdir(html_dir):
            all_html_names = {
                _name_key(fn) for fn in os.listdir(html_dir)
                if fn.lower().endswith(".html")}
    except (RuntimeError, ValueError, OSError) as exc:
        logger.warning("[StagePairs] HTML 全量索引失败（本轮整组保留）: %s", exc)
        return
    paired_json: set[str] = set()
    units: list[dict] = []
    for html_path in html_paths:
        companion = _stage_companion_path(html_path, json_dir)
        has_json = bool(companion and os.path.isfile(companion))
        if has_json:
            paired_json.add(os.path.normcase(companion))
            owner = _stage_json_skill_key(companion)
            if owner and owner != target_key:
                logger.warning(
                    "[StagePairs] 同名快照归属其他技能（整对保留）: %s",
                    companion)
                continue
        units.append({"html": html_path, "json": companion if has_json else ""})
    if json_dir and os.path.isdir(json_dir):
        try:
            json_names = sorted(os.listdir(json_dir))
        except OSError as exc:
            logger.warning("[StagePairs] JSON 目录不可枚举（本轮整组保留）: %s", exc)
            return
        for name in json_names:
            path = os.path.join(json_dir, name)
            if not os.path.isfile(path) or not name.lower().endswith(".json"):
                continue
            if os.path.normcase(path) in paired_json:
                continue
            stem = os.path.splitext(name)[0]
            if _name_key(f"{stem}.html") in all_html_names:
                continue
            if not stage_of_file(stem + ".html"):
                continue
            owner = _stage_json_skill_key(path)
            if not owner:
                logger.debug(
                    "[StagePairs] 孤儿快照无归属（保留并交由显式迁移）: %s",
                    path)
                continue
            if owner != target_key:
                logger.debug(
                    "[StagePairs] 孤儿快照归属其他技能（保留）: %s", path)
                continue
            units.append({"html": "", "json": path})
    units.sort(key=_pair_sort_key, reverse=True)
    deleted_html = 0
    deleted_json = 0
    for unit in units[keep:]:
        html_path = unit.get("html") or ""
        json_path = unit.get("json") or ""
        if protect_ts > 0 and any(
                _is_round_protected(path, protect_ts)
                for path in (html_path, json_path)
                if path and os.path.isfile(path)):
            continue
        has_html = bool(html_path and os.path.isfile(html_path))
        has_json = bool(json_path and os.path.isfile(json_path))
        if not (has_html or has_json):
            continue
        if not _recycle_stage_unit(skill_dir, html_path, json_path):
            logger.debug("[StagePairs] 配对回收未完成（保留）: %s / %s",
                         html_path, json_path)
            continue
        if has_html:
            deleted_html += 1
            summary["deleted"] += 1
            summary["groups"]["htm"] = summary["groups"].get("htm", 0) + 1
        if has_json:
            deleted_json += 1
            summary["deleted"] += 1
            summary["groups"]["stage_json"] = (
                summary["groups"].get("stage_json", 0) + 1)
    summary["kept"]["htm"] = len(html_paths) - deleted_html
    summary["kept"]["stage_json"] = (
        sum(1 for unit in units if unit.get("json")) - deleted_json)
def _namespace_content_owned(dir_path: str, skill_dir: str) -> bool:
    target = normalize_skill_key(skill_dir)
    if not target:
        return False
    try:
        names = sorted(os.listdir(dir_path))
    except OSError as exc:
        logger.debug("[StagePairs] 命名空间内容探测失败: %s: %s", dir_path, exc)
        return False
    owned_by_target = False
    for name in names:
        path = os.path.join(dir_path, name)
        if not name.lower().endswith(".json") or not os.path.isfile(path):
            return False
        owner = _stage_json_skill_key(path)
        if not owner or owner != target:
            return False
        owned_by_target = True
    return owned_by_target
def _namespace_owned_by_skill(dir_path: str, skill_dir: str) -> bool:
    raw = os.path.basename(os.path.normpath(skill_dir)) or ""
    if not raw.strip():
        return False
    base = os.path.normcase(safe_ns(raw))
    name = os.path.basename(os.path.normpath(dir_path))
    folded = os.path.normcase(name)
    if folded == base:
        return _namespace_content_owned(dir_path, skill_dir)
    if not folded.startswith(base + "-"):
        return False
    suffix = folded[len(base) + 1:]
    if len(suffix) != 8 or any(ch not in "0123456789abcdef" for ch in suffix):
        return False
    try:
        canonical = os.path.normcase(path_scoped_namespace(skill_dir))
    except (OSError, RuntimeError, ValueError) as exc:
        logger.debug("[StagePairs] 规范命名空间解析失败: %s: %s", skill_dir, exc)
        canonical = ""
    if canonical and folded == canonical:
        return True
    return _namespace_content_owned(dir_path, skill_dir)
def _unique_target(target: str, *, is_dir: bool = False) -> str:
    if not os.path.lexists(target):
        return target
    root, ext = (target, "") if is_dir else os.path.splitext(target)
    stamp = int(time.time() * 1000)
    candidate = f"{root}.{stamp}{ext}"
    index = 1
    while os.path.lexists(candidate):
        candidate = f"{root}.{stamp}-{index}{ext}"
        index += 1
    return candidate
def _move_artifact(src: str, dst: str, dry_run: bool, result: dict) -> bool:
    item = {"from": src, "to": dst}
    if dry_run:
        result["plan"].append(item)
        return True
    try:
        if os.path.lexists(dst):
            raise FileExistsError(f"迁移目标已存在: {dst}")
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        # 统一走 shutil.move：os.rename 跨文件系统（EXDEV）必失败，而迁移源
        # （旧 htm/zhenduan）与目标（Temp 归档）可能落在不同卷；
        # shutil.move 同卷等价 rename，跨卷自动降级 copy+unlink。
        shutil.move(src, dst)
    except OSError as exc:
        result["errors"].append({
            **item, "error": f"{type(exc).__name__}: {exc}"})
        return False
    result["moved"].append(item)
    return True
def _rollback_moved_artifact(item: dict, result: dict) -> bool:
    rollback = {"from": item["to"], "to": item["from"]}
    try:
        if os.path.lexists(rollback["to"]):
            raise FileExistsError(f"回滚目标已存在: {rollback['to']}")
        os.makedirs(os.path.dirname(rollback["to"]), exist_ok=True)
        # 回滚与正向迁移同口径：跨卷回滚同样需要 copy+unlink 兜底。
        shutil.move(rollback["from"], rollback["to"])
    except OSError as exc:
        result["errors"].append({
            **rollback, "error": f"rollback {type(exc).__name__}: {exc}"})
        return False
    result["moved"].remove(item)
    return True
def migrate_legacy_report_artifacts(skill_dir: str, *, dry_run: bool = True) -> dict:
    dry_run = True if dry_run is None else signal_bool(dry_run)
    result = {
        "dry_run": dry_run,
        "plan": [],
        "moved": [],
        "skipped": [],
        "errors": [],
        "summary": {
            "unpaired_html": 0,
            "ownerless_html": 0,
            "orphan_json": 0,
            "non_stage_json": 0,
            "legacy_dirs": 0,
            "planned": 0,
            "moved": 0,
        },
    }
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        result["errors"].append({"error": "缺少技能归属锚"})
        return result
    try:
        skill_dir = normalize_skill_dir(skill_dir)
    except (OSError, TypeError, ValueError) as exc:
        result["errors"].append({"error": f"技能归属锚归一失败: {exc}"})
        return result
    try:
        html_dir = get_html_report_base()
        json_dir = json_root_dir(skill_dir)
        temp_root = json_artifact_dir(skill_dir)
    except (RuntimeError, ValueError) as exc:
        result["errors"].append({"error": f"落点解析失败: {exc}"})
        return result
    target_json_dir = os.path.join(temp_root, "legacy_zhenduan")
    target_html_dir = os.path.join(temp_root, "legacy_htm")
    html_listed = _listdir_join(
        html_dir, lambda fn: fn.lower().endswith(".html"), "旧 HTML")
    json_listed = _listdir_join(json_dir, lambda _fn: True, "旧 JSON 根")
    if html_listed is None or json_listed is None:
        result["errors"].append({"error": "旧布局目录不可枚举，迁移中止"})
        return result
    html_files = []
    for path in html_listed:
        if os.path.isfile(path):
            html_files.append(path)
        else:
            result["skipped"].append({"path": path, "reason": "not_a_file"})
    html_names = {os.path.basename(path) for path in html_files}
    json_names = sorted(os.path.basename(path) for path in json_listed)
    json_name_by_key = {_name_key(name): name for name in json_names}
    protected_json = {
        _name_key(f"{os.path.splitext(fn)[0]}.json") for fn in html_names}
    target_key = normalize_skill_key(skill_dir)
    if html_names:
        for name in sorted(html_names):
            path = os.path.join(html_dir, name)
            meta = read_stage_meta(path)
            owner = normalize_skill_key(meta.get("skill") or "")
            if owner and owner != target_key:
                result["skipped"].append({"path": path, "reason": "other_skill"})
                continue
            companion_name = f"{os.path.splitext(name)[0]}.json"
            companion_key = _name_key(companion_name)
            actual_companion_name = json_name_by_key.get(
                companion_key, companion_name)
            companion = os.path.join(json_dir, actual_companion_name)
            has_json = (companion_key in json_name_by_key
                        and os.path.isfile(companion))
            if has_json:
                companion_owner = _stage_json_skill_key(companion)
                if companion_owner and companion_owner != target_key:
                    result["skipped"].append({
                        "path": path, "reason": "companion_other_skill"})
                    continue
            if owner and has_json:
                continue
            if owner:
                result["summary"]["unpaired_html"] += 1
            else:
                result["summary"]["ownerless_html"] += 1
            html_target = _unique_target(os.path.join(target_html_dir, name))
            html_item = {"from": path, "to": html_target}
            html_moved = _move_artifact(path, html_target, dry_run, result)
            if has_json:
                if not html_moved:
                    result["skipped"].append({
                        "path": companion, "reason": "html_move_failed"})
                    continue
                json_moved = _move_artifact(
                    companion,
                    _unique_target(os.path.join(target_json_dir, companion_name)),
                    dry_run, result)
                if not json_moved and _rollback_moved_artifact(html_item, result):
                    result["skipped"].append({
                        "path": path, "reason": "json_move_failed"})
    if json_names:
        for name in json_names:
            path = os.path.join(json_dir, name)
            if os.path.isdir(path):
                if name.startswith("_"):
                    continue
                if not _namespace_owned_by_skill(path, skill_dir):
                    result["skipped"].append({
                        "path": path, "reason": "other_skill_namespace"})
                    continue
                result["summary"]["legacy_dirs"] += 1
                _move_artifact(
                    path, _unique_target(os.path.join(target_json_dir, name),
                                         is_dir=True), dry_run, result)
                continue
            if (not name.lower().endswith(".json")
                    or _name_key(name) in protected_json):
                continue
            owner = _stage_json_skill_key(path)
            if owner and owner != target_key:
                result["skipped"].append(
                    {"path": path, "reason": "other_skill"})
                continue
            stem = os.path.splitext(name)[0]
            kind = ("orphan_json" if stage_of_file(stem + ".html")
                    else "non_stage_json")
            result["summary"][kind] += 1
            _move_artifact(
                path, _unique_target(os.path.join(target_json_dir, name)),
                dry_run, result)
    result["summary"]["planned"] = len(result["plan"])
    result["summary"]["moved"] = len(result["moved"])
    return result
_DEFAULT_PROTECT_TS = 0.0
_KEEP_REPORTS = 8
_KEEP_FIX_RESULTS = 60
_KEEP_HTML = 120
def _normalize_keep(value: Any, default: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        return default
    return value if value >= 0 else default
def _is_valid_protect_ts(value: Any) -> bool:
    return (not isinstance(value, bool)
            and isinstance(value, (int, float))
            and (not isinstance(value, float) or math.isfinite(value))
            and value >= 0)
def prune_consumed_artifacts(
    skill_dir: str,
    *,
    protect_ts: float = _DEFAULT_PROTECT_TS,
    keep_reports: int = _KEEP_REPORTS,
    keep_fix_results: int = _KEEP_FIX_RESULTS,
    keep_html: int = _KEEP_HTML,
) -> dict:
    summary = {"deleted": 0, "groups": {}, "kept": {}}
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        logger.warning("[PruneConsumed] 缺少技能归属锚（不执行裁剪）")
        return summary
    if not _is_valid_protect_ts(protect_ts):
        logger.warning(
            "[PruneConsumed] 非法轮次保护点（不执行裁剪）: %r", protect_ts)
        return summary
    keep_reports = _normalize_keep(keep_reports, _KEEP_REPORTS)
    keep_fix_results = _normalize_keep(keep_fix_results, _KEEP_FIX_RESULTS)
    keep_html = _normalize_keep(keep_html, _KEEP_HTML)
    try:
        temp_dir = get_temp_dir(skill_dir)
    except (RuntimeError, ValueError) as exc:
        logger.warning("[PruneConsumed] Temp 归口不可解析（跳过裁剪）: %s", exc)
        return summary
    _paths = (_collect_temp_grouped_paths(temp_dir)
              if os.path.isdir(temp_dir)
              else {key: [] for key in _PRUNE_GROUP_KEYS})
    if _paths is None:
        return summary
    _paths["aifix_bak"] += _collect_backup_group_paths(temp_dir)
    _keep_of = {"reports": keep_reports, "fix_results": keep_fix_results,
                "none": 0}
    _unknown_sources = sorted({src for _key, src, _group in _PRUNE_PLAN
                               if src not in _keep_of})
    if _unknown_sources:
        logger.warning("[PruneConsumed] 未声明保留来源 %s（整轮跳过裁剪）",
                       _unknown_sources)
        return summary
    for key, keep_src, group_name in _PRUNE_PLAN:
        _prune_artifact_group(_paths[key], _keep_of[keep_src], group_name,
                              protect_ts, summary)
    _prune_stage_pairs(skill_dir, keep_html, protect_ts, summary)
    return summary
def prune_stage_artifacts(skill_dir: str, *, protect_ts: float) -> dict:
    summary: dict = {"backup_prune": None, "consumed_artifacts": None}
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        logger.warning("[ArtifactPrune] 缺少技能归属锚（跳过收尾回收）")
        return summary
    try:
        skill_dir = normalize_skill_dir(skill_dir)
    except (OSError, TypeError, ValueError) as exc:
        logger.warning("[ArtifactPrune] 技能归属锚归一失败（跳过收尾回收）: %s", exc)
        return summary
    try:
        _backup = prune_backups(get_backup_root(skill_dir))
    except Exception as _be:  # noqa: BLE001 — 备份裁剪软失败不阻断收尾
        logger.warning("[ArtifactPrune] 备份裁剪异常（已忽略）: %s", _be)
    else:
        summary["backup_prune"] = _backup
        if _backup and (_backup.get("deleted_files")
                        or _backup.get("deleted_dirs")):
            logger.info("[ArtifactPrune] 备份裁剪: %s", _backup)
    try:
        _artifacts = prune_consumed_artifacts(skill_dir, protect_ts=protect_ts)
    except Exception as _ae:  # noqa: BLE001 — 一次性产物清理软失败不阻断收尾
        logger.warning("[ArtifactPrune] 一次性产物清理异常（已忽略）: %s", _ae)
        return summary
    summary["consumed_artifacts"] = _artifacts
    if _artifacts and _artifacts.get("deleted"):
        logger.info("[ArtifactPrune] 一次性产物清理: 删 %d 项, 明细 %s",
                    _artifacts["deleted"], _artifacts.get("groups", {}))
    return summary
_SCRATCH_ARTIFACTS: frozenset[str] = frozenset({
    "baseline", "_baseline", "t5_regression_metrics.json",
    "incremental_snapshot", "governance_baseline.json",
    "governance_decisions.jsonl", "governance_acceptance.jsonl",
})
_SCRATCH_DESTINATION_RESOLVERS = {
    "t5_regression_metrics.json": t5_baseline_path,
    "governance_baseline.json": governance_baseline_path,
    "governance_decisions.jsonl": governance_decisions_path,
    "governance_acceptance.jsonl": governance_acceptance_path,
}
def _legacy_name_map() -> dict[str, tuple[str, str]]:
    mapping: dict[str, tuple[str, str]] = {}
    for section, legacy in EVOLUTION_STATE_SECTIONS.items():
        mapping[os.path.normcase(legacy)] = ("section", section)
    for name in EVOLUTION_AUX_ARTIFACTS.values():
        mapping[os.path.normcase(name)] = ("root", name)
    for name in _SCRATCH_ARTIFACTS:
        mapping[os.path.normcase(name)] = ("scratch", name)
    return mapping
def _move_into(path: str, target_dir: str) -> str | None:
    os.makedirs(target_dir, exist_ok=True)
    dest = os.path.join(target_dir, os.path.basename(path))
    if os.path.exists(dest):
        logger.warning(
            "[ArtifactMigrate] 目标已存在，跳过覆盖（保留源文件）: %s -> %s",
            path, dest)
        return None
    try:
        shutil.move(path, dest)
        return dest
    except (OSError, shutil.Error) as exc:
        logger.warning("[ArtifactMigrate] 迁移失败: %s -> %s: %s",
                       path, dest, exc)
        return None
def migrate_legacy_evolution_artifacts(skill_dir: str, *,
                                        dry_run: bool = True) -> dict:
    dry_run = True if dry_run is None else signal_bool(dry_run)
    sd = _dir_arg(skill_dir)
    if not sd:
        return {"ok": False, "error": "缺少技能归属锚", "migrated": [],
                "skipped": []}
    sd = normalize_skill_dir(sd)
    try:
        jdir = get_jinhua_dir(sd)
    except (RuntimeError, ValueError) as exc:
        return {"ok": False, "error": str(exc), "migrated": [], "skipped": []}
    if not os.path.isdir(jdir):
        return {"ok": True, "migrated": [], "skipped": [],
                "note": "jinhua 目录不存在（无需迁移）"}
    legacy_map = _legacy_name_map()
    migrated: list[dict] = []
    skipped: list[dict] = []
    for name in sorted(os.listdir(jdir)):
        if name in EVOLUTION_ROOT_ARTIFACTS:
            continue
        if name == EVOLUTION_SCRATCH_DIRNAME:
            continue
        full = os.path.join(jdir, name)
        key = os.path.normcase(name)
        if key.endswith(".lock"):
            migrated.append({"ok": True, "name": name, "kind": "lock",
                             "dry_run": dry_run, "recycle": full})
            continue
        if name == "memory_injection_receipt.jsonl":
            record = _migrate_receipt_events(sd, full, dry_run=dry_run)
            (migrated if record.get("ok") else skipped).append(record)
            continue
        if name.endswith("retrospective_report.json"):
            continue
        target = legacy_map.get(key)
        if target is None:
            skipped.append({"name": name, "reason": "unregistered"})
            continue
        kind, dest = target
        if kind == "root":
            continue
        if kind == "section":
            record = _migrate_section(sd, name, dest, full, dry_run=dry_run)
        else:
            resolver = _SCRATCH_DESTINATION_RESOLVERS.get(name)
            destination = (resolver(sd) if resolver is not None
                           else os.path.join(evolution_scratch_dir(sd), dest))
            dest_dir = os.path.dirname(destination)
            new_path = None if dry_run else _move_into(full, dest_dir)
            record = {
                "ok": dry_run or new_path is not None,
                "name": name,
                "kind": "scratch",
                "dest": new_path or destination,
                "dry_run": dry_run,
            }
        (migrated if record.get("ok") else skipped).append(record)
    if not dry_run:
        completed = []
        for record in migrated:
            recycle = record.get("recycle")
            if recycle:
                if safe_delete(recycle):
                    record["recycled"] = True
                else:
                    record.update(
                        ok=False, reason=f"recycle_failed: {recycle}")
                    skipped.append(record)
                    continue
            completed.append(record)
        migrated = completed
    return {"ok": True, "skill_dir": sd, "jinhua_dir": jdir,
            "dry_run": dry_run, "migrated": migrated, "skipped": skipped}
def _migrate_section(skill_dir: str, name: str, section: str, full: str,
                     *, dry_run: bool) -> dict:
    data, status, error = read_json_artifact(full)
    if status == "missing":
        return {"ok": False, "name": name, "kind": "section",
                "section": section, "reason": "missing_source: 旧 section 文件不存在"}
    if status != "ok":
        return {"ok": False, "name": name, "kind": "section",
                "section": section, "reason": f"parse_error: {error or status}"}
    record = {"ok": True, "name": name, "kind": "section",
              "section": section, "dry_run": dry_run}
    if dry_run:
        return record
    container = read_evolution_state(skill_dir)
    if section in container:
        if container[section] != data:
            return {"ok": False, "name": name, "kind": "section",
                    "section": section,
                    "reason": "section_conflict: 统一容器与旧文件内容不一致"}
        record["note"] = "section 已存在且内容一致，旧文件去重回收"
    elif not write_evolution_section(skill_dir, section, data):
        return {"ok": False, "name": name, "kind": "section",
                "section": section, "reason": "write_failed"}
    record["recycle"] = full
    return record
def _migrate_receipt_events(skill_dir: str, full: str, *,
                            dry_run: bool) -> dict:
    record = {"ok": True, "name": os.path.basename(full),
              "kind": "events", "dry_run": dry_run}
    try:
        with open(full, encoding="utf-8-sig") as handle:
            events = []
            for line_number, line in enumerate(handle, 1):
                text = line.strip()
                if not text:
                    continue
                try:
                    payload = json.loads(text)
                except (ValueError, RecursionError) as exc:
                    record.update(
                        ok=False,
                        reason=(f"parse_error: line {line_number}: "
                                f"{type(exc).__name__}"),
                    )
                    return record
                if not isinstance(payload, dict):
                    record.update(
                        ok=False,
                        reason=f"invalid_event: line {line_number} 必须是 JSON 对象",
                    )
                    return record
                events.append(payload)
    except UnicodeError as exc:
        return {"ok": False, "name": os.path.basename(full),
                "kind": "events", "reason": f"decode_error: {exc}"}
    except OSError as exc:
        return {"ok": False, "name": os.path.basename(full),
                "kind": "events", "reason": str(exc)}
    record["count"] = len(events)
    if dry_run:
        return record
    if events:
        appended, _skipped = append_evolution_events(
            skill_dir, events,
            dedup_fields=("round_start_ts", "content_sha256"))
        record["appended"] = appended
        if appended + _skipped != len(events):
            record.update(
                ok=False,
                skipped=_skipped,
                reason=(f"append_incomplete: {len(events)} 条事件仅确认 "
                        f"{appended + _skipped} 条（新增+重复）"),
            )
            return record
    record["recycle"] = full
    return record
def _jinhua_scan_context(skill_dir: str, action: str,
                         registry: tuple | None = None,
                         ) -> tuple[str, tuple] | None:
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        logger.warning("[ArtifactScan] 缺少技能归属锚，%s跳过", action)
        return None
    jdir = _resolve_jinhua_dir(normalize_skill_dir(skill_dir), action)
    if jdir is None:
        return None
    return jdir, _specs_for_scope("jinhua", registry)
def scan_unregistered_jinhua_artifacts(skill_dir: str, *,
                                       registry: tuple | None = None) -> list:
    ctx = _jinhua_scan_context(skill_dir, "扫描", registry)
    if ctx is None:
        return []
    jdir, specs = ctx
    return _scan_scope_artifacts(
        jdir, specs, allow_root_markdown=_JINHUA_ALLOW_ROOT_MARKDOWN)
def is_unregistered_jinhua_artifact(skill_dir: str, relative_path: str, *,
                                     registry: tuple | None = None) -> bool:
    relative_text = fs_path_text(relative_path)
    if not relative_text.strip():
        return False
    normalized = os.path.normpath(relative_text)
    if (os.path.isabs(normalized) or os.path.splitdrive(normalized)[0]
            or "\x00" in normalized
            or normalized in (".", "..")
            or normalized.startswith(".." + os.sep)):
        return False
    ctx = _jinhua_scan_context(skill_dir, "文件判定", registry)
    if ctx is None:
        return False
    _jdir, specs = ctx
    parts = [part for part in normalized.split(os.sep) if part]
    if not parts or any(part == ".." for part in parts):
        return False
    if len(parts) > 1:
        return _name_key(parts[0]) not in _dir_names(specs)
    if (_JINHUA_ALLOW_ROOT_MARKDOWN and _is_human_doc_name(parts[0])):
        return False
    return not _is_registered_name(
        parts[0], specs, allow_lock_derivatives=_ALLOW_LOCK_DERIVATIVES)
def _unscoped_entry_finding(artifact: str, index: int,
                            record: dict) -> dict:
    return {
        "artifact": artifact,
        "index": index,
        "locator": str(record.get("locator") or ""),
        "round_start_ts": str(record.get("round_start_ts") or ""),
    }


def _scan_unscoped_json_entries(path: str, artifact: str) -> list[dict]:
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            document = json.load(handle)
    except (OSError, ValueError, RecursionError) as exc:
        logger.debug("[ArtifactScan] %s 不可读，条目作用域扫描跳过: %s",
                     artifact, exc)
        return []
    entries = document.get("entries") if isinstance(document, dict) else None
    if not isinstance(entries, list):
        return []
    return [
        _unscoped_entry_finding(artifact, index, entry)
        for index, entry in enumerate(entries)
        if isinstance(entry, dict)
        and not str(entry.get("project") or "").strip()
    ]


def _scan_unscoped_jsonl_entries(path: str, artifact: str) -> list[dict]:
    findings: list[dict] = []
    try:
        with open(path, encoding="utf-8-sig", errors="replace") as handle:
            for index, line in enumerate(handle):
                text = line.strip()
                if not text:
                    continue
                try:
                    record = json.loads(text)
                except (ValueError, RecursionError):
                    continue
                if (isinstance(record, dict)
                        and not str(record.get("project") or "").strip()):
                    findings.append(
                        _unscoped_entry_finding(artifact, index, record))
    except OSError as exc:
        logger.debug("[ArtifactScan] %s 不可读，条目作用域扫描跳过: %s",
                     artifact, exc)
        return []
    return findings


def scan_unscoped_jinhua_entries(skill_dir: str) -> list[dict]:
    """定位类账本条目必须带项目作用域（``project``）。

    共享账本后 ``_human_confirmations.json`` 的 ``locator`` 与
    ``cv_conclusion_history.jsonl`` 的 ``conclusions`` 都是项目内相对定位：
    缺 ``project`` 的条目会在所有项目上生效（跨项目误抑制真问题）。该检查
    只报告，不进入删除流水线（删整个文件会丢掉其他项目的合法账本）。
    """
    ctx = _jinhua_scan_context(skill_dir, "条目作用域扫描")
    if ctx is None:
        return []
    jdir, _specs = ctx
    findings: list[dict] = []
    findings.extend(_scan_unscoped_json_entries(
        os.path.join(jdir, "_human_confirmations.json"),
        "_human_confirmations.json"))
    findings.extend(_scan_unscoped_jsonl_entries(
        os.path.join(jdir, "cv_conclusion_history.jsonl"),
        "cv_conclusion_history.jsonl"))
    return findings


def scan_unregistered_jinhua_dirs(skill_dir: str, *,
                                   registry: tuple | None = None) -> list:
    ctx = _jinhua_scan_context(skill_dir, "目录扫描", registry)
    if ctx is None:
        return []
    jdir, specs = ctx
    if not os.path.isdir(jdir):
        return []
    registered_dirs = _dir_names(specs)
    try:
        names = os.listdir(jdir)
    except OSError as exc:
        logger.warning("[ArtifactScan] jinhua 列目录失败，目录扫描跳过: %s", exc)
        return []
    return sorted(
        name for name in names
        if _is_unregistered_root_dir(jdir, name, registered_dirs))
def is_unregistered_jinhua_dir(
        skill_dir: str, dir_name: str, *, registry: tuple | None = None,
        allow_absent: bool = False) -> bool:
    dir_name = fs_path_text(dir_name)
    if not dir_name:
        return False
    if (dir_name in (".", "..") or os.path.splitdrive(dir_name)[0]
            or "\x00" in dir_name):
        return False
    if os.sep in dir_name or (os.altsep and os.altsep in dir_name):
        return False
    ctx = _jinhua_scan_context(skill_dir, "目录判定", registry)
    if ctx is None:
        return False
    jdir, specs = ctx
    if not allow_absent and not os.path.isdir(jdir):
        return False
    return _is_unregistered_root_dir(
        jdir, dir_name, _dir_names(specs), allow_absent=allow_absent)
def scan_unregistered_log_artifacts(skill_dir: str, *,
                                     registry: tuple | None = None) -> list:
    del skill_dir
    log_dir = get_log_dir()
    if not log_dir:
        logger.warning("[ArtifactScan] log 目录不可解析，扫描跳过")
        return []
    return _scan_scope_artifacts(
        log_dir, _specs_for_scope("log", registry),
        allow_lock_derivatives=True, allow_root_markdown=True)
def scan_unregistered_temp_artifacts(skill_dir: str, *,
                                      registry: tuple | None = None) -> list:
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        logger.warning("[ArtifactScan] 缺少技能归属锚，Temp 扫描跳过")
        return []
    try:
        temp_dir = get_temp_base(normalize_skill_dir(skill_dir))
    except (RuntimeError, ValueError) as exc:
        logger.warning("[ArtifactScan] Temp 归口不可解析，扫描跳过: %s", exc)
        return []
    if not os.path.isdir(temp_dir):
        return []
    try:
        names = os.listdir(temp_dir)
    except OSError as exc:
        logger.warning("[ArtifactScan] Temp 列目录失败，扫描跳过: %s", exc)
        return []
    specs = _specs_for_scope("temp", registry)
    return sorted(
        name for name in names
        if _is_unregistered_temp_handoff(temp_dir, name, specs))
def _is_unregistered_temp_handoff(temp_dir: str, name: str,
                                  specs: tuple) -> bool:
    if not os.path.isfile(os.path.join(temp_dir, name)):
        return False
    return not _is_registered_name(
        name, specs, allow_lock_derivatives=_ALLOW_LOCK_DERIVATIVES)
def _resolve_jinhua_dir(skill_dir: str, action: str) -> str | None:
    try:
        return get_jinhua_dir(skill_dir)
    except (RuntimeError, ValueError) as exc:
        logger.warning("[ArtifactScan] jinhua 目录不可解析，%s跳过: %s",
                       action, exc)
        return None
def _dir_names(specs: tuple) -> set:
    return {_name_key(s.name) for s in specs if s.match == "dir"}
def _is_unregistered_root_dir(
        jdir: str, name: str, registered: set, *,
        allow_absent: bool = False) -> bool:
    return (_name_key(name) not in registered
            and (allow_absent or os.path.isdir(os.path.join(jdir, name))))
def _on_walk_error(exc: OSError) -> None:
    logger.warning("[ArtifactScan] 目录枚举失败，已跳过: %s", exc)
_ALLOW_LOCK_DERIVATIVES = False
_ALLOW_ROOT_MARKDOWN = False
_JINHUA_ALLOW_ROOT_MARKDOWN = False
def _scan_scope_artifacts(scope_dir: str, specs: tuple,
                          allow_lock_derivatives: bool = _ALLOW_LOCK_DERIVATIVES,
                          allow_root_markdown: bool = _ALLOW_ROOT_MARKDOWN) -> list:
    if not os.path.isdir(scope_dir):
        return []
    dir_names = _dir_names(specs)
    unregistered: list = []
    for root, dirs, files in os.walk(scope_dir, onerror=_on_walk_error):
        rel_dir = os.path.relpath(root, scope_dir)
        top = rel_dir.split(os.sep)[0] if rel_dir != "." else ""
        if top and _name_key(top) in dir_names:
            dirs[:] = []
            continue
        _append_unregistered_files(
            files, rel_dir, specs, unregistered,
            allow_lock_derivatives=allow_lock_derivatives,
            allow_root_markdown=allow_root_markdown)
    return sorted(unregistered)
def _append_unregistered_files(files: list, rel_dir: str, specs: tuple,
                                out: list, *,
                                allow_lock_derivatives: bool,
                                allow_root_markdown: bool) -> None:
    for fn in files:
        if (allow_root_markdown and rel_dir == "."
                and _is_human_doc_name(fn)):
            continue
        if (rel_dir == "." and _is_registered_name(
                fn, specs, allow_lock_derivatives=allow_lock_derivatives)):
            continue
        rel = fn if rel_dir == "." else os.path.join(rel_dir, fn)
        out.append(rel)
_LOCK_SUFFIX = ".lock"
_HUMAN_DOC_SUFFIXES = (".md", ".markdown", ".rst")
def _is_human_doc_name(name: str) -> bool:
    return name.lower().endswith(_HUMAN_DOC_SUFFIXES)
_PRUNE_TMP_MARKER = ".prune_tmp."
_name_key = os.path.normcase
def _is_registered_name(fn: str, specs: tuple,
                        allow_lock_derivatives: bool) -> bool:
    raw_candidates = [fn]
    if allow_lock_derivatives and _name_key(fn).endswith(_LOCK_SUFFIX):
        raw_candidates.append(fn[: -len(_LOCK_SUFFIX)])
    derived = []
    for cand in raw_candidates:
        folded = _name_key(cand)
        if _PRUNE_TMP_MARKER in folded:
            derived.append(cand[:folded.index(_PRUNE_TMP_MARKER)])
    candidates = raw_candidates + derived
    return any(
        (s.match == "exact" and _name_key(s.name) == _name_key(cand))
        or (s.match == "prefix" and _name_key(cand).startswith(
            _name_key(s.name)))
        or (s.match == "suffix" and _name_key(cand).endswith(
            _name_key(s.name)))
        for cand in candidates for s in specs)
def _is_within_dir(real_path: str, real_dir: str) -> bool:
    path = os.path.normcase(os.path.abspath(real_path))
    root = os.path.normcase(os.path.abspath(real_dir))
    if path == root:
        return True
    return path.startswith(root if root.endswith(os.sep) else root + os.sep)
def _is_active_log_name(fname: str) -> bool:
    folded = _name_key(fname)
    return any(_name_key(name) == folded for name in ACTIVE_FILES)
def _classify_log_file(fname: str, target_dir: str, real_target: str,
                       cutoff_ts: float) -> tuple[str, str]:
    fpath = os.path.join(target_dir, fname)
    if os.path.islink(fpath):
        return "skip", ""
    try:
        real_fpath = os.path.realpath(fpath)
    except OSError as e:
        logger.debug("cleanup_old_logs: realpath failed for %s: %s", fpath, e)
        return "skip", ""
    if not _is_within_dir(real_fpath, real_target):
        logger.debug("cleanup_old_logs: skipping path outside log dir: %s", fpath)
        return "skip", ""
    if not os.path.isfile(fpath):
        return "ignore", ""
    if _is_active_log_name(fname) or _name_key(fname).endswith(_LOCK_SUFFIX):
        return "skip", ""
    try:
        mtime = os.path.getmtime(fpath)
    except OSError as e:
        logger.debug("cleanup_old_logs: stat failed for %s: %s", fname, e)
        return "error", f"{fname}: {e}"
    if mtime < cutoff_ts:
        return "expired", fpath
    return "skip", ""
def _reap_expired_files(fnames: list[str], target_dir: str,
                        real_target: str,
                        cutoff_ts: float) -> tuple[int, int, list[str]]:
    deleted = 0
    skipped = 0
    errors: list[str] = []
    for fname in fnames:
        verdict, detail = _classify_log_file(
            fname, target_dir, real_target, cutoff_ts)
        if verdict == "ignore":
            continue
        if verdict == "skip":
            skipped += 1
            continue
        if verdict == "error":
            errors.append(detail)
            continue
        try:
            if safe_delete(detail):
                deleted += 1
            else:
                errors.append(f"{fname}: safe_delete failed")
        except OSError as e:
            logger.debug("cleanup_old_logs: delete failed for %s: %s", fname, e)
            errors.append(f"{fname}: {e}")
    return deleted, skipped, errors
def _zero_cleanup_result(log_dir: str,
                         errors: list[str] | None = None) -> dict[str, Any]:
    return {
        "deleted": 0,
        "skipped": 0,
        "errors": list(errors or []),
        "log_dir": log_dir,
    }
def _cleanup_days_error(max_days: int) -> str:
    if (isinstance(max_days, bool)
            or not isinstance(max_days, (int, float))
            or (isinstance(max_days, float) and not math.isfinite(max_days))):
        return f"max_days must be a finite number >= 0, got: {max_days!r}"
    if max_days < 0:
        return f"max_days must be >= 0, got: {max_days}"
    return ""
def _open_cleanup_target(max_days: int,
                         log_dir: str | None) -> tuple[str, list[str], dict | None]:
    if log_dir is None:
        target_dir = get_log_dir() or ""
    else:
        try:
            raw_dir = os.fsdecode(os.fspath(log_dir)).strip()
        except (TypeError, ValueError):
            return "", [], _zero_cleanup_result(
                "", [f"log_dir must be a path, got: {log_dir!r}"])
        if not raw_dir or raw_dir in (".", os.curdir):
            target_dir = get_log_dir() or ""
        else:
            target_dir = expand_git_bash_path(raw_dir)
            if not os.path.isabs(target_dir):
                return "", [], _zero_cleanup_result(
                    "", [f"log_dir must be an absolute path, got: {log_dir!r}"])
    days_error = _cleanup_days_error(max_days)
    if days_error:
        return target_dir, [], _zero_cleanup_result(target_dir, [days_error])
    if not target_dir:
        return target_dir, [], _zero_cleanup_result(target_dir)
    if not os.path.isdir(target_dir):
        if os.path.exists(target_dir):
            return target_dir, [], _zero_cleanup_result(
                target_dir, [f"log_dir is not a directory: {target_dir}"])
        return target_dir, [], _zero_cleanup_result(target_dir)
    try:
        fnames = os.listdir(target_dir)
    except OSError as e:
        logger.debug("cleanup_old_logs: listdir failed for %s: %s", target_dir, e)
        return target_dir, [], _zero_cleanup_result(
            target_dir, [f"listdir failed: {e}"])
    return target_dir, fnames, None
_SECONDS_PER_DAY = 86400.0
_DEFAULT_LOG_RETENTION_DAYS = 30
def _expiry_cutoff_ts(max_days: int) -> float:
    now = time.time()
    if max_days > now / _SECONDS_PER_DAY:
        return float("-inf")
    return now - float(max_days) * _SECONDS_PER_DAY
def cleanup_old_logs(max_days: int = _DEFAULT_LOG_RETENTION_DAYS,
                     log_dir: str | None = None) -> dict[str, Any]:
    target_dir, fnames, guard = _open_cleanup_target(max_days, log_dir)
    if guard is not None:
        return guard
    cutoff_ts = _expiry_cutoff_ts(max_days)
    real_target = os.path.realpath(target_dir)
    deleted, skipped, errors = _reap_expired_files(
        fnames, target_dir, real_target, cutoff_ts)
    logger.info("cleanup_old_logs: deleted=%d, skipped=%d, errors=%d",
                deleted, skipped, len(errors))
    return {"deleted": deleted, "skipped": skipped, "errors": errors, "log_dir": target_dir}
def run_post_completion_governance(
    skill_dir: str,
    out: dict,
    *,
    protect_ts: float = _DEFAULT_PROTECT_TS,
) -> None:
    skill_dir = _dir_arg(skill_dir)
    if not skill_dir:
        logger.warning("[AutoEnhanceStep] 缺少技能归属锚（跳过收尾回收）")
        return
    if not isinstance(out, dict):
        logger.warning("[AutoEnhanceStep] 收尾结果载体非 dict（%s），跳过回收",
                       type(out).__name__)
        return
    try:
        _pruned = prune_stage_artifacts(skill_dir, protect_ts=protect_ts)
    except Exception as _pe:  # noqa: BLE001 — 回收入口不可用不阻断收尾
        logger.warning("[AutoEnhanceStep] 收尾回收异常（已忽略）: %s", _pe)
        return
    if not isinstance(_pruned, dict):
        return
    if _pruned.get("backup_prune") is not None:
        out["_backup_prune"] = _pruned["backup_prune"]
    if _pruned.get("consumed_artifacts") is not None:
        out["_consumed_artifacts_prune"] = _pruned["consumed_artifacts"]

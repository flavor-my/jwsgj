# jwsgj 模块索引

根目录共 **307 个 `.py` 文件**：**305 个域模块 + 2 个入口**（包门面与 CLI 入口，见域 1），合计 **307 个可导入文件**，按 17 个能力域归类、每个文件只出现一次；`tests/` 目录用于回归测试（按 `test_<module>.py` 命名），不计入模块清单。文末另附 **225 个包级入口函数**速查。

用法：按文件名或前缀定位所属域 → 回 `SKILL.md`「入口归属与导入」找包级入口；需要函数级定位时查文末「入口函数速查」。未列在表中的入口只在模块级提供，按 `jwsgj.<module>.<function>` 导入。`skill_profile.json` 的 `layer_map` 与本文域划分同源，覆盖全部 306 个模块名（`__init__` 由 `domain_prefixes` 单独登记）。

## 目录

| # | 域 | 可导入文件 | 职责 |
| --- | --- | --- | --- |
| 1 | 运行底座与公开面 | 12 | 包级导出、CLI 运行时、路径/缓存/日志、技能画像 |
| 2 | 管线编排 | 8 | 相位推进、文本触发、批次调度、报告装配与交付追溯 |
| 3 | 诊断内核 | 116 | 文件/AST/调用图/盲区/安全/污点/评分/门禁/台账 |
| 4 | 六域引擎 A–F | 15 | 质量、内聚与历史、安全、符号执行、变异与死代码 |
| 5 | 交叉验证 | 14 | 证据通道、置信度、仲裁、阈值学习与误报过滤 |
| 6 | 预防规则与代码引用 | 19 | 规则 ID、代码引用表、写前检查与预防提示 |
| 7 | 构建与生成 | 40 | 创建预检、发现匹配、模板/脚本、文档重写、安全写盘 |
| 8 | 技能治理与修复 | 12 | 文档诊断/渲染/重构守卫、审计规则与扫描内核 |
| 9 | 治疗与重构 | 14 | 治疗状态/证据、源码重写、迁移、验收与 API 契约 |
| 10 | 复盘与反馈 | 7 | 复盘分析、质量评分、消费链、反馈协调与留痕 |
| 11 | 反哺与记忆 | 5 | 日志驱动进化、记忆桥、反馈与操作生成 |
| 12 | 测试与覆盖率 | 18 | 覆盖率、静态/运行时分析、变异、性能与测试套件 |
| 13 | 清理与共存 | 7 | 死代码/残留/文件卫生、新旧实现与架构共存 |
| 14 | 报告渲染 | 5 | 诊断/管线/审核报告与 HTML 构件 |
| 15 | AI 审核 | 5 | 待审队列、条目通道、条目计划、治理判定与执行 |
| 16 | 幻觉防护 | 3 | 写前规范、台账与幻觉预检 |
| 17 | 扇出与反馈 | 7 | 同族缺陷、代码反馈、误报判定与日志模式 |

合计 307 个可导入文件（305 个域模块 + 2 个入口）。

## 1. 运行底座与公开面（12）

包级导出面、CLI 运行时、路径与缓存、日志配置、技能画像。

- 入口：`__init__.py`、`__main__.py`
- 契约与运行时：`build_contract.py`、`cli_skill_runtime.py`、`log_config.py`
- 路径与缓存：`runtime_paths.py`、`runtime_scope.py`、`shared_cache.py`、`shared_cache_store.py`
- 画像与组合面：`skill_profile.py`、`surface_build.py`、`surface_diag.py`

## 2. 管线编排（8）

16 相位推进、文本触发、批次调度、进度恢复、报告装配与交付追溯。

- 调度与推进：`build_pipeline.py`、`build_pipeline_checks.py`、`pipeline_steps_phases.py`、`pipeline_trigger_route.py`
- 轮次与报告：`build_full_analysis.py`、`pipeline_round_trace.py`、`pipeline_report_assembly.py`、`pipeline_report_delivery.py`

## 3. 诊断内核（116）

文件/AST/调用图/盲区/安全/污点/评分/门禁/台账。前缀族：`diag_shared_*`（共享 AST 与源码底座）、`diag_gate_*`（门禁 B 规则族）、`diag_guard_*`（守卫与红线）、`diag_traps_*`（陷阱检测）、`diag_taint_*`（污点）、`diag_se_*`（安全证据）、`diag_wiring_*`（接线与导入）、`diag_rules_*`（规则包）。

- 反模式与坏味：`diag_antipattern.py`、`diag_antipattern_flow_detect.py`、`diag_antipattern_flow_govern.py`、`diag_smell_detector.py`、`diag_pattern_rules.py`、`diag_debt_engine.py`
- 共享底座：`diag_shared_ast_bindings.py`、`diag_shared_ast_nodes.py`、`diag_shared_ast_surface.py`、`diag_shared_ast_views.py`、`diag_shared_source_core.py`、`diag_shared_source_scan.py`、`diag_types_defs.py`、`diag_types_normalize.py`、`diag_types_vocab.py`
- 调用图：`diag_callgraph_builder.py`、`diag_callgraph_channels.py`、`diag_callgraph_collect.py`、`diag_callgraph_facts.py`、`diag_callgraph_resolve.py`、`diag_callgraph_source.py`、`diag_callgraph_verdicts.py`、`diag_implicit_calls.py`
- 盲区：`diag_blindspot_file.py`、`diag_blindspot_refs.py`、`diag_blindspot_report.py`、`diag_blindspot_symbol.py`
- 门禁 B 族：`diag_gate_arch.py`、`diag_gate_class.py`、`diag_gate_class_protocol.py`、`diag_gate_expr.py`、`diag_gate_expr_flow.py`、`diag_gate_io_control.py`、`diag_gate_loop.py`、`diag_gate_scope_bind.py`
- 守卫与红线：`diag_guard_dirfile.py`、`diag_guard_injection_enforce.py`、`diag_guard_injection_scan.py`、`diag_guard_io.py`、`diag_guard_quality.py`、`diag_guard_scale.py`、`diag_guard_source.py`、`diag_guard_sql_connection.py`、`diag_guard_sql_statement.py`、`diag_guard_state.py`
- 陷阱检测：`diag_traps_async.py`、`diag_traps_binding.py`、`diag_traps_blocking.py`、`diag_traps_coding.py`、`diag_traps_guard.py`、`diag_traps_payload.py`
- 安全证据：`diag_se_data.py`、`diag_se_injection.py`、`diag_se_knowledge.py`、`diag_se_stdlib.py`、`diag_security_diagnoser.py`
- 污点分析：`diag_taint_dataflow.py`、`diag_taint_interproc.py`、`diag_taint_model.py`、`diag_taint_scanners.py`、`diag_taint_symbolic.py`、`diag_taint_tracker.py`
- 接线与导入：`diag_wiring_exc.py`、`diag_wiring_exc_flow.py`、`diag_wiring_import_scan.py`、`diag_wiring_imports.py`、`diag_wiring_symbol_scan.py`
- 规则包：`diag_rules_api_risk.py`、`diag_rules_expr_forms.py`、`diag_rules_numeric_guard.py`、`diag_rules_py_syntax.py`、`diag_rules_runtime.py`、`diag_rules_text_damage.py`、`diag_solidify_rules.py`、`diag_structure_rules.py`
- 结构与表面：`diag_module_surface.py`、`diag_module_topology.py`、`diag_symbol_integrity.py`、`diag_symbol_surface.py`、`diag_structure_arch.py`、`diag_verify_contract.py`
- 门禁与台账：`diag_zero_backlog_gate.py`、`diag_zero_backlog_ledger.py`、`diag_delivery_gate.py`、`diag_delivery_integrity_gate.py`、`diag_merge_safety.py`
- 依赖与健康：`diag_dependency_analyzer.py`、`diag_dependency_core.py`、`diag_health_profile.py`、`diag_health_scoring.py`、`diag_ten_dim_scorer.py`
- 扫描与执行：`diag_file_scanner.py`、`diag_method_invoke.py`、`diag_detector_assembly.py`、`diag_detector_findings.py`、`diag_detectors_registry.py`、`diag_audit_container.py`、`diag_audit_none_guard.py`、`diag_exception_detection.py`、`diag_exception_verdict.py`、`diag_regression_exec.py`、`diag_regression_guard.py`、`diag_runtime_forensics.py`、`diag_runtime_objects.py`
- 审查与覆盖：`diag_incremental_review.py`、`diag_log_coverage.py`、`diag_coverage_runtime.py`、`diag_coverage_scan.py`、`diag_warning_quality.py`
- 模拟执行：`diag_simulate_evidence.py`、`diag_simulate_runner.py`、`diag_simulate_sandbox.py`、`diag_business_flow.py`
- 计划与写前门禁：`diag_split_plan.py`、`diag_split_gate.py`、`diag_self_check.py`

## 4. 六域引擎 A–F（15）

缺陷与文档一致性、内聚与历史、安全、符号执行、变异、死代码专用引擎。

- A 组：`engine_a1_defects.py`、`engine_a1_name_flow.py`、`engine_a1_structure.py`、`engine_a3_silent_degrade.py`、`engine_a4_doc_code.py`
- B 组：`engine_b1_cohesion.py`、`engine_b2_history.py`
- D 组：`engine_d1_static.py`、`engine_d1_tool_channels.py`、`engine_d2_flow.py`、`engine_d2_symbolic.py`、`engine_d2_verdict.py`、`engine_d_security.py`
- E/F 组：`engine_e2_mutation.py`、`engine_f_deadcode.py`

## 5. 交叉验证（14）

证据通道、置信度复核、仲裁、阈值学习、误报过滤。

- 证据与结论：`xv_evidence_channels.py`、`xv_evidence_crosscheck.py`、`xv_evidence_strength.py`、`xv_conclusion_engine.py`、`xv_findings_core.py`
- 上下文与存储：`xv_context_derivation.py`、`xv_context_history.py`、`xv_intermediate_store.py`
- 裁决与报告：`xv_arbiter.py`、`xv_confidence_review.py`、`xv_rule_checks.py`、`xv_threshold_learning.py`、`xv_fp_filter_stages.py`、`xv_cv_report_assemble.py`

## 6. 预防规则与代码引用（19）

规则 ID、代码引用表、写前检查与预防提示注入。

- 引用表：`prevention_refs_main.py`、`prevention_diag_refs.py`、`prevention_ext_refs.py`、`prevention_logic_refs.py`、`prevention_method_refs.py`、`prevention_write_refs.py`
- 参数与容器：`prevention_arg_checks.py`、`prevention_container_length.py`、`prevention_container_mutation.py`
- 流程与作用域：`prevention_flow_exit_checks.py`、`prevention_flow_loop_checks.py`、`prevention_scope_checks.py`、`prevention_scope_facts.py`
- 字面量与语言质量：`prevention_literal_protocol.py`、`prevention_literal_truth.py`、`prevention_lang_quality.py`
- 生成与写前：`prevention_gen_checks.py`、`prevention_write_checks.py`、`prevention_diag_extra.py`

## 7. 构建与生成（40）

创建预检、发现匹配、模板/脚本生成、文档重写、拆分与安全写盘。

- 预检与预介入：`build_preflight.py`、`build_preflight_guard.py`、`build_preintervention.py`、`preintervention_engines.py`
- 可发现性与匹配：`build_discover_sixdim.py`、`build_discover_sixdim_text.py`、`build_discover_text_doc.py`、`build_matching_diagnoser.py`、`build_skill_discovery.py`
- 文档生成与优化：`build_skill_md_generate.py`、`build_skill_md_optimize.py`、`build_skill_md_quality.py`、`build_skill_md_rewrite.py`、`build_skill_merge.py`、`build_skill_module_scan.py`、`build_skill_quality_a2.py`、`build_text_document.py`、`build_text_frontmatter.py`、`build_text_scoring.py`、`build_text_signals.py`
- 触发面：`build_trigger_activation.py`、`build_trigger_evaluate.py`
- 健康与生命周期：`build_skill_health.py`、`build_skill_lifecycle.py`、`build_skill_consistency.py`、`build_skill_api_contract.py`
- 质量与架构门禁：`build_code_quality.py`、`build_arch_gate.py`、`build_module_topology.py`、`build_import_reference.py`、`build_import_time_guard.py`
- 重构与写盘：`build_refactor_collect.py`、`build_refactor_gate.py`、`build_refactor_plan.py`、`build_refactor_policy.py`、`build_safe_orchestration.py`、`build_safe_rollback.py`、`build_safe_write.py`
- 脚本与合规：`build_script_compliance.py`、`build_script_generation.py`

## 8. 技能治理与修复（12）

文档诊断/渲染/重构守卫、审计规则与扫描内核。

- 文档流水线：`skill_doc_diagnoser.py`、`skill_doc_render.py`、`skill_doc_structure.py`、`skill_doc_subdim_content.py`、`skill_doc_refactor_guard.py`
- 审计与扫描：`skill_audit_rules.py`、`skill_scan_kernels.py`
- 修复引导与安全：`fix_guide_knowledge.py`、`fix_guide_rule_identity.py`、`fix_safety_boundary.py`、`fix_safety_gate.py`、`fix_safety_verify.py`

## 9. 治疗与重构（14）

治疗计划/状态/证据、源码重写、迁移、验收与 API 契约、拆分与大函数分解。

- 治疗：`treatment_plan.py`、`treatment_state.py`、`treatment_evidence.py`、`treatment_verdict.py`、`treatment_experience.py`、`treatment_feedback.py`
- 重构动作：`refactor_split_actions.py`、`refactor_decompose_actions.py`、`refactor_source_rewrite.py`、`refactor_write_actions.py`
- 迁移与验收：`refactor_migration_prepare.py`、`refactor_migration_commit.py`、`refactor_post_validation.py`、`refactor_api_contract.py`

## 10. 复盘与反馈（7）

复盘分析、质量评分、消费链核验、反馈协调与留痕。

- `fupan_analyzer.py`、`fupan_engine.py`、`feedback_coordinator.py`
- `retrospective_audit.py`、`retrospective_enhancer.py`、`retrospective_evolution.py`、`retrospective_ledger.py`

## 11. 反哺与记忆（5）

日志驱动进化、记忆桥、反馈与操作生成。

- `log_driven_evolution.py`、`memory_bridge.py`、`memory_bridge_ops.py`、`memory_feedback_core.py`、`memory_op_generation.py`

## 12. 测试与覆盖率（18）

覆盖率实测、静态/运行时分析、变异、性能与测试套件。

- 测试诊断：`diag_testing_coverage.py`、`diag_testing_import_audit.py`、`diag_testing_metrics.py`、`diag_testing_source.py`、`diag_testing_static.py`、`diag_testing_test_index.py`
- 扫描与运行时：`diag_testing_scan_ast.py`、`diag_testing_scan_sca.py`、`diag_testing_runtime.py`
- 变异与性能：`diag_testing_mutation.py`、`diag_testing_mutation_runtime.py`、`diag_testing_perf.py`、`diag_testing_perf_metrics.py`
- 套件：`testsuite_coverage_map.py`、`testsuite_eval.py`、`testsuite_orchestrator.py`、`testsuite_registry.py`、`testsuite_runner.py`

## 13. 清理与共存（7）

死代码/残留/文件卫生、新旧实现与架构共存分析。

- 共存：`arch_coexistence_pairs.py`、`arch_coexistence_scan.py`、`coexistence_cleaner.py`、`coexistence_detect.py`
- 清理：`cleanup_artifacts.py`、`cleanup_file_hygiene.py`、`cleanup_residue.py`

## 14. 报告渲染（5）

诊断/管线/审核报告与 HTML 基础构件。

- `html_render_diag.py`、`html_render_pipeline.py`、`html_render_review.py`、`html_report_primitives.py`、`html_report_stage_doc.py`

## 15. AI 审核（5）

待审队列、条目通道、条目计划、治理判定与执行。

- `ai_review_governance.py`、`ai_review_governance_review.py`、`ai_review_item_channels.py`、`ai_review_item_plan.py`、`ai_review_queue.py`

## 16. 幻觉防护（3）

写前规范、台账与幻觉预检。

- `hallucination_norms.py`、`hallucination_ledger.py`、`hallucination_prewrite.py`

## 17. 扇出与反馈（7）

同族缺陷汇总、代码反馈分级、误报判定与日志模式分析。

- `fanout_governance.py`、`fanout_report.py`、`fp_rules_judge.py`、`log_analysis.py`
- `code_feedback_cv_rules.py`、`code_feedback_thresholds.py`、`code_level_feedback_l2.py`

## 入口函数速查（225）

`__init__.py` 的 326 个包级导出中，可直接调用的入口函数共 225 个（另有 50 个类与异常、51 个常量）。除 `SKILL.md`「入口归属与导入」标注了模块路径的入口外，均可 `from jwsgj import <name>` 导入。

### 1. 运行底座与公开面（12）（6）

| 入口 | 职责 |
| --- | --- |
| `get_backup_base` | 解析备份根目录（工作空间 Temp/_backups），拒绝写入技能根 |
| `get_series_rule_ids` | 按诊断系列名返回该系列的全部规则 ID |
| `get_temp_base` | 解析技能隔离的运行态根目录，无工作空间时抛错 |
| `get_warmed_cache` | 预热并取回共享缓存实例，供引擎入口复用 |
| `list_diag_series` | 列出全部诊断系列名称 |
| `setup_logging` | 初始化技能日志（目录、级别、JSON 与终端开关） |

### 2. 管线编排（8）（30）

| 入口 | 职责 |
| --- | --- |
| `aggregate_report` | 聚合各阶段中间产物为完整管线报告 |
| `build_review_out` | 装配阶段 5 复盘输出结构 |
| `describe_pipeline_field_flow` | 描述管线报告字段流向（字段→阶段映射） |
| `diag_skill` | 对单个技能执行轻量诊断并返回报告 |
| `diag_skill_security` | 技能级安全诊断入口（污点/注入/路径穿越） |
| `get_diagnosis_progress` | 读取诊断阶段进度与断点 |
| `get_pipeline_progress` | 读取整条管线的相位、完成度与下一步动作 |
| `get_pipeline_round_trace` | 按轮次读取管线执行轨迹 |
| `get_pipeline_stage_traces` | 读取指定阶段的轨迹明细，可按相位过滤 |
| `get_treatment_progress` | 读取治疗阶段进度与待处理条目 |
| `query_methods_progress` | 按方法粒度查询诊断进度视图（相位与断点） |
| `guarded_step` | 装饰器/上下文：为管线步骤加载守卫与留痕 |
| `register_backlog_soft` | 把报告中的软销项登记进归零台账 |
| `run_ai_manual_fix_step` | 阶段 4b：AI 手工修复批次推进 |
| `run_auto_enhance_step` | 阶段 6e：报告记忆增强与交付门禁串行裁决 |
| `run_code_feedback_step` | 阶段 6c：代码级反馈沉淀 |
| `run_cv_step` | 阶段 2b：交叉验证主通道推进 |
| `run_diagnosis_step` | 阶段 1：诊断推进，可按 method_id 单点重跑 |
| `run_dry_route_step` | 阶段 G：扇出路由预演 |
| `run_feedback_loop_step` | 阶段 6b：反馈闭环推进 |
| `run_fupan_step` | 阶段 6a：复盘产出质量分与记忆操作 |
| `run_health_diag` | 运行技能健康诊断（quick 可只跑快检） |
| `run_next_pipeline_step` | 单步推进管线到下一相位并返回断点 |
| `run_pipeline_batch` | 批量推进管线，最多 max_steps 步，遇阻则早停 |
| `run_pipeline_from_trigger` | 从用户原话触发完整管线，execute=False 仅探测 |
| `run_regression_cv_step` | 阶段 2a：回归交叉验证推进 |
| `run_review_step` | 阶段 5：复盘审核推进，可输出 HTML |
| `run_stage5_review` | 阶段 5 复盘装配（诊断/交叉验证/方案三路结果） |
| `run_treatment_plan_step` | 阶段 3b：治疗方案生成 |
| `run_treatment_step` | 阶段 4：按条目索引执行治疗 |

### 3. 诊断内核（116）（22）

| 入口 | 职责 |
| --- | --- |
| `aaf_verify_diag` | 写前门禁：诊断结论一致性校验 |
| `aaf_verify_patch_precheck` | 写前门禁：补丁落地前置校验 |
| `audit_log_coverage` | 审计日志埋点覆盖、运行时暴露与静默通道 |
| `build_dependency_graph` | 构建模块依赖图（可允许缺失节点） |
| `build_symbol_universe` | 构建项目符号全集，供符号级比对使用 |
| `check_memory_injection_gate` | 门禁 4：复盘记忆注入质量核验 |
| `check_precision_gate` | 门禁 2a：精确证据守卫裁决 |
| `check_zero_backlog` | 门禁 1：归零门禁，统计未终态 finding |
| `describe_verdict_trace_keys` | 描述判定轨迹的字段结构 |
| `ensure_tool` | 检测外部工具可用性，缺失时按需 pip 补装 |
| `fanout_residual_gate` | 扇出残留门禁：同族位点未处置即阻断 |
| `get_ai_review_verdicts` | 读取指定轮次/通道的 AI 审核判定 |
| `get_entry_guard` | 获取写前入口守卫实例 |
| `get_size_guard` | 获取注入内容体积守卫 |
| `ground_code_symbols` | 把代码中的符号落地到项目定义（幻觉接地） |
| `maint_health_check` | 维护态健康自检（门面可导入性/版本/依赖） |
| `preflight_diagnostic_check` | 诊断类代码的写前预检 |
| `preflight_symbol_check` | 符号存在性写前预检 |
| `profile_test_performance` | 剖析测试性能，定位慢用例与瓶颈样本 |
| `quick_guard` | 一站式写前守卫：代码片段快速拦截 |
| `run_health` | 运行健康评估（五维/十维评分的统一入口） |
| `scan_boundary_imports` | 扫描跨层非法导入与循环依赖 |

### 4. 六域引擎 A–F（15）（8）

| 入口 | 职责 |
| --- | --- |
| `build_clean_plan` | 构建死代码清理方案（含再导出映射） |
| `build_fixed_sources` | 按方案生成修复后的源码映射 |
| `cross_validate_deadcode` | 死代码候选交叉验证，剔除误报 |
| `result_to_b1_findings` | 把 B1 内聚分析结果转为标准 findings |
| `run_a3_silent_degrade` | A3 静默降级检测引擎入口 |
| `run_b1_unified_ast_analysis` | B1 统一 AST 分析引擎入口（内聚/复杂度） |
| `run_deadcode_cleanup` | 死代码清理入口，默认 dry_run=True 只出方案 |
| `run_security_analysis` | 安全分析引擎入口（污点/注入/危险调用） |

### 5. 交叉验证（14）（1）

| 入口 | 职责 |
| --- | --- |
| `build_ai_fix_list` | 交叉验证后生成 AI 修复清单 |

### 6. 预防规则与代码引用（19）（7）

| 入口 | 职责 |
| --- | --- |
| `enrich_diag_findings` | 为诊断发现补充规则代码引用 |
| `enrich_entry_result` | 为入口结果补充代码引用与规范提示 |
| `get_code_reference` | 按规则 ID 取代码引用条目 |
| `list_code_ref_rule_ids` | 列出具备代码引用的规则 ID |
| `list_logic_rule_ids` | 列出逻辑类预防规则 ID |
| `preflight_api_check` | API 使用类写前检查 |
| `resolve_code_ref` | 解析规则 ID 对应的代码引用（含回退） |

### 7. 构建与生成（40）（17）

| 入口 | 职责 |
| --- | --- |
| `auto_crystallize` | 操作名/模块名自动结晶为规则候选 |
| `build_preflight` | 技能创建预检：契约、结构与资源声明 |
| `create_skill_doc` | 生成技能初稿（名称/领域/能力/关键词） |
| `detect_skill_overlaps` | 检测技能间重叠与职责冲突 |
| `evaluate_trigger_feedback` | 评估触发反馈并给出词表调整建议 |
| `get_calibrator` | 获取触发阈值校准器 |
| `get_content_quality_rules` | 获取内容质量规则集 |
| `get_module_consumers` | 查询模块的消费方（fan-in） |
| `get_standard_sections` | 获取标准章节注册表 |
| `match_pipeline_trigger` | 强词匹配：返回命中的强制管线关键词 |
| `probe_pipeline_trigger` | 三层漏斗触发探测：强词/弱词语境门/模糊近义 |
| `quick_match_skills` | 按查询语句快速匹配候选技能（top-k） |
| `quick_route` | 按用户意图快速路由到目标技能 |
| `recommend_cold_start` | 冷启动推荐：为新技能建议关键词与近义表达 |
| `run_guided_creation` | 引导式创建：命名、骨架与 SKILL.md 初稿 |
| `suggest_pair_resolution` | 对重叠技能对给出消解建议 |
| `trigger_feedback_message` | 把触发反馈装配为可读消息 |

### 8. 技能治理与修复（12）（12）

| 入口 | 职责 |
| --- | --- |
| `aaf_verify_behavior` | 写前门禁：行为等价性校验 |
| `aaf_verify_hallucination_precheck` | 写前门禁：幻觉预检 |
| `aaf_verify_inline` | 写前门禁：内联片段校验 |
| `aaf_verify_syntax_safety` | 写前门禁：语法安全性校验 |
| `apply_refactored_doc` | 采纳文档重构方案：先备份再写回并复检 |
| `apply_security_write` | 安全写入：目标校验通过后落盘修复源码 |
| `deduplicate_security_findings` | 安全发现去重合并 |
| `diag_skill_doc` | 文档评分入口：返回五维分数与问题清单 |
| `diag_skill_doc_to_markdown` | 把文档评分结果渲染为 Markdown 报告 |
| `get_fix_order_for_findings` | 为发现项计算修复顺序与依赖 |
| `refactor_skill_doc` | 生成 SKILL.md 重构方案，auto_apply=False 只产方案 |
| `validate_section_registry` | 校验标准章节注册表的一致性 |

### 9. 治疗与重构（14）（20）

| 入口 | 职责 |
| --- | --- |
| `analyze_growth` | 对比新旧目录的体量与复杂度增长 |
| `apply_ai_fix` | 按索引采纳 AI 修复结果 |
| `build_diagnosis_evidence` | 为治疗条目构建诊断证据（含代码片段） |
| `build_fix_step_out` | 装配单步修复输出（后端与耗时） |
| `evaluate_zero_leftover` | 评估残留是否归零并给出结论 |
| `execute_treatment_item_core` | 治疗条目核心执行逻辑（按索引） |
| `extract_code_context` | 按文件与行号抽取上下文代码 |
| `extract_code_context_in_project` | 项目内按相对路径抽取代码上下文 |
| `generate_treatment_plan` | 生成治疗方案（诊断+修复路由+额外发现） |
| `get_ai_fix_candidates` | 列出 AI 修复候选（含经验摘要） |
| `get_effective_adjustments` | 读取生效中的治疗反馈调整项 |
| `locate_treatment_item` | 按索引定位治疗条目 |
| `plan_single_fix` | 为单条发现规划修复步骤 |
| `preview_targeted_tests` | 预览定向回归测试范围 |
| `run_ai_manual_fix` | AI 手工修复批次执行（可 dry_run） |
| `run_feedback_loop` | 治疗反馈闭环：汇总修复路由与记忆上下文 |
| `run_fix_backend` | 按后端执行修复（LLM 或规则） |
| `run_guard` | 重构前后六约束守护检查 |
| `run_refactor_execution` | 执行重构，默认 dry_run=True |
| `run_refactor_workflow` | 重构工作流：full/阶段化推进，可续跑 |

### 10. 复盘与反馈（7）（23）

| 入口 | 职责 |
| --- | --- |
| `analyze_session` | 分析会话消息、工具调用与错误 |
| `apply_approved_fix` | 采纳已审核通过的修复方案 |
| `clear_feedback_history` | 清空反馈历史（受控重置） |
| `close_loop_check` | 闭环检查：确认工具使用与结果一致 |
| `collect_diagnostic_defense_signals` | 采集诊断防御信号（矛盾/回归） |
| `detect_fupan` | 判定是否需要复盘 |
| `detect_fupan_execution` | 按任务类型判定复盘执行需求 |
| `detect_risks` | 从文本中识别风险项 |
| `fp_consume_event_risks` | 消费事件风险并登记误报改进 |
| `fp_consume_log_growth` | 消费日志增长风险并登记改进 |
| `get_pending_enhancements` | 读取待应用的记忆增强项 |
| `get_retrospective_history` | 读取复盘历史 |
| `mark_enhancement_applied` | 标记增强项已应用 |
| `quick_analyze` | 快速复盘分析（消息/工具/错误） |
| `record_defense_feedback` | 记录防御反馈（矛盾与回归状态） |
| `run_fupan` | 执行复盘，产出摘要、风险与改进项 |
| `run_retrospective` | 复盘沉淀入口：聚合诊断与治疗产物 |
| `run_stage6a_fupan` | 阶段 6a 复盘装配（审核+执行结果） |
| `score_dimensions` | 按任务成功/错误数/耗时/改码计算质量分 |
| `should_fupan` | 复盘触发判定 |
| `summarize_defense_feedback` | 汇总防御反馈结论 |
| `verify_consumption_chain` | 核验产物消费链是否闭合 |
| `verify_fupan_writes` | 核验复盘产物是否真实落盘 |

### 11. 反哺与记忆（5）（8）

| 入口 | 职责 |
| --- | --- |
| `compute_information_density` | 计算文本信息密度 |
| `evaluate_memory_density` | 评估记忆条目的信息密度 |
| `extract_rule_candidates` | 从消费记录中提取规则候选 |
| `get_memory_search_queries` | 生成记忆检索查询语句 |
| `get_pre_creation_search_queries` | 生成创建前查重检索语句 |
| `prepare_diagnostic_context` | 装配诊断上下文（检索结果+既有记忆） |
| `register_rule_candidates` | 登记规则候选待固化 |
| `run_log_driven_evolution` | 日志驱动进化：候选挖掘与规则沉淀 |

### 12. 测试与覆盖率（18）（6）

| 入口 | 职责 |
| --- | --- |
| `analyze_test_coverage` | 分析测试覆盖率并给出缺口 |
| `get_coverage_report` | 读取覆盖率报告 |
| `get_rule_fallback` | 取规则的回退等级定义 |
| `locate_targeted_tests` | 按改动文件定位定向测试 |
| `run_targeted_regression` | 执行定向回归（可设超时） |
| `summarize_regression` | 汇总回归结果 |

### 13. 清理与共存（7）（17）

| 入口 | 职责 |
| --- | --- |
| `analyze_file` | 分析单文件卫生状况（残留/临时产物） |
| `apply_cleanup_fix` | 执行已审核的清理计划 |
| `artifact_registry` | 读取/登记产物登记表 |
| `check_locator_scope_integrity` | 定位类账本条目的项目作用域完整性门禁（只读） |
| `check_stub_constraints_for_content` | 校验内容是否触碰兼容桩约束 |
| `describe_evolution_artifact_keys` | 描述进化产物的键结构 |
| `detect_new_compat_stubs` | 检测新增兼容桩（对比变更文件） |
| `enqueue_arch_coexistence_plans` | 把架构共存发现入队为清理计划 |
| `enqueue_cleanup_plan` | 把清理项入队为待审计划 |
| `get_stub_constraints` | 读取兼容桩约束清单 |
| `quick_arch_coexistence_scan` | 架构共存快速扫描 |
| `quick_cleanup` | 一键清理分析，默认 dry_run=True |
| `quick_coexistence_scan` | 新旧实现共存快速扫描 |
| `reject_cleanup_plan` | 驳回清理计划并记录理由 |
| `scan_stubs` | 兼容桩/门户文件存量盘点 |
| `scan_unregistered_jinhua_artifacts` | 扫描未登记的 jinhua 产物 |
| `scan_unregistered_temp_artifacts` | 扫描未登记的 Temp 产物 |

### 14. 报告渲染（5）（18）

| 入口 | 职责 |
| --- | --- |
| `collect_html_artifacts` | 收集 HTML 产物路径（含额外目录） |
| `format_impact_report` | 渲染影响面报告文本 |
| `generate_html_report` | 统一 HTML 报告生成入口 |
| `render_ai_review_html` | 渲染 AI 审核报告 HTML |
| `render_batch_report_html` | 渲染批量执行报告 HTML |
| `render_blindspot_report_html` | 渲染盲区扫描报告 HTML |
| `render_coverage_report_html` | 渲染覆盖率报告 HTML |
| `render_cv_report_html` | 渲染交叉验证报告 HTML |
| `render_dependency_report_html` | 渲染依赖分析报告 HTML |
| `render_diagnosis_report_html` | 渲染诊断报告 HTML |
| `render_file_scan_report_html` | 渲染文件扫描报告 HTML |
| `render_fupan_report_html` | 渲染复盘报告 HTML |
| `render_health_report_html` | 渲染健康评估报告 HTML |
| `render_pipeline_report_html` | 渲染管线报告 HTML |
| `render_pipeline_summary_html` | 渲染管线摘要 HTML |
| `render_retro_report_html` | 渲染复盘沉淀报告 HTML |
| `render_security_report_html` | 渲染安全审计报告 HTML |
| `render_treatment_item_html` | 渲染单条治疗条目 HTML |

### 15. AI 审核（5）（10）

| 入口 | 职责 |
| --- | --- |
| `apply_ai_fix_batch` | 批量应用 AI 修复（受 max_items 限制） |
| `apply_approved_adjustment` | 采纳已批准的调整项 |
| `apply_cv_uncertain_verdict` | 写入交叉验证不确定项的判定 |
| `describe_review_item_keys` | 描述审核条目字段结构 |
| `fixate_fp_rules` | 固化误报规则（默认最少 3 次命中） |
| `list_pending_ai_reviews` | 列出待 AI 审核条目 |
| `run_all_ai_reviews` | 批量审核全部待审条目 |
| `run_next_ai_review` | 审核下一条待审条目 |
| `set_ai_review_provider` | 注册审核提供方（批量审核复用） |
| `validate_review_assessment` | 校验审核评估（拓扑/验证结果） |

### 16. 幻觉防护（3）（4）

| 入口 | 职责 |
| --- | --- |
| `attach_code_refs` | 为约束附加代码引用 |
| `get_constraints_for_task` | 按任务类型取写前约束 |
| `inject_code_refs_to_prompt` | 把代码引用注入提示词 |
| `inject_full_prevention_prompt` | 注入完整写前预防提示 |

### 17. 扇出与反馈（7）（16）

| 入口 | 职责 |
| --- | --- |
| `analyze_log_patterns` | 按消费者分析日志模式 |
| `analyze_perf_bottlenecks` | 按阈值与退化比定位性能瓶颈 |
| `build_fanout_findings` | 把扇出报告转为标准 findings |
| `check_log_quality` | 检查日志质量（埋点完整性） |
| `fanout_evolution_signal` | 产出扇出进化信号 |
| `fanout_module_counts` | 统计扇出涉及的模块分布 |
| `fanout_pre_treatment_gate` | 治疗前扇出门禁 |
| `fanout_treatment_handoff` | 扇出到治疗的交接数据 |
| `get_template_stats` | 读取注入模板统计 |
| `query_logs` | 按过滤条件查询日志 |
| `reconstruct_pipeline_execution` | 按 trace_id 与时间窗重建管线执行序列 |
| `register_injection_template` | 登记注入模板 |
| `run_fanout_diagnosis` | 缺陷扇出诊断入口 |
| `scan_signatures` | 扫描同族缺陷签名位点 |
| `select_fanout_strategy` | 按缺陷族选择扇出策略 |
| `summarize_fanout_strategies` | 汇总扇出策略与命中情况 |


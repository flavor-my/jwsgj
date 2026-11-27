---
name: jwsgj
description: "jwsgj 是面向 AgentSkill 与 Python 代码库的全链路治理内核，只读取证与写盘执行严格分离。当用户要创建、体检、评分、诊断、审计、审查、重构或治理 AgentSkill / Python 项目时使用本技能——包括「帮我看下这个技能」「SKILL.md 太长/读不完」「技能为什么总不被触发」「全读技能根目录文件」「提炼整合去重文档」「清死代码」「跑一遍测试」「看下调用链」「查依赖拓扑」「误报复核」「预演重构」「验收回滚」「提交前跑交付门禁」「报错/异常/跑不通」「按代码行为重构 SKILL.md」等口语请求。出现 BUG、缺陷、扇出、测试、诊断、治疗、验证、审计、分析、检查、优化、死代码、清理任一强词即视为治理意图，必须跑完整管线，不得单步探测；看下、查查、检查下、诊断下、分析下、优化下、修一下、改一下、帮我看看、过一遍、跑一下同样触发。只读诊断与写盘分离，方案与预演不授予写盘权限。核心能力：技能创建预检、骨架与初稿、创建后复检、重叠检测、打包与版本提升；SKILL.md 全读、提炼整合去重、文档提分与重排、可发现性优化、description 与触发覆盖审计、排查技能为何不被路由、评分回归；扫描反模式、调用链断裂、循环依赖、跨层导入、注入、污点、路径穿越、空桩、死代码、兼容桩、架构共存、模拟运行异常与静默退化；采集覆盖率、定位慢用例与复杂度热点、审计日志埋点与静默通道、生成 HTML 报告；交叉验证误报漏报、归零门禁、重构预演、拆分、迁移、基线、六项验收、管线推进与断点续跑、复盘反哺规则与记忆。常见场景：技能体检、文档提分、安全审计、重构验收、交付门禁；面向开发者、测试、安全审计、架构师与管理者；英文 skill review / code review / static analysis / safety audit / dead code / refactor / audit / coverage / pipeline / gate 同样适用。命令行用 python -m jwsgj，编程用 jwsgj 包级入口；也可调整 skill 目录结构（长文档拆到 references/ 或 scripts/、删除过时内容、按 AgentSkills 规范校验）。不适用于业务功能开发、非代码产物生成、数据库运维与线上发布；主要产出为文档排版或页面交互时不属于本技能。"
version: 3.336.0
keywords:
  - 技能治理
  - 诊断
  - 治疗
  - 复盘
  - 反哺进化
  - 死代码
  - 重构
  - 安全审计
  - 测试覆盖率
  - 依赖拓扑
  - 调用链
  - 门禁
  - 误报复核
  - 静默失败
  - 技能路由
  - 文档提分
  - AgentSkill
  - skill governance
  - dead code
  - refactor
  - audit
  - coverage
  - pipeline
  - quality gate
dependencies:
  python: ">=3.10"
  packages:
    pip:
      - "PyYAML>=6.0"
      - "psutil>=5.9"
      - "z3-solver>=4.12"
      - "coverage>=7.0"
      - "pytest>=7.0"
      - "tomli>=2.0; python_version < '3.11'"
---

# jwsgj · AgentSkill 与 Python 全链路治理内核

**固定工作流**：确认对象与授权 → 只读诊断 → 复核证据 → 生成方案 → 取得授权 → 写盘执行 → 回归验证与门禁推进。`diag_*` / `xv_*` / `scan_*` 只读取证，不改目标源码；治疗、文档采纳、清理执行与回滚必须单独授权并留痕——**证据、方案与预演都不等于写盘授权**。单点复核走 CLI，多阶段组合走 API，两者共用同一套实现。

当前规模：`import jwsgj` 提供 **326 个包级导出**（225 个入口函数 + 50 个类与异常 + 51 个常量），`python -m jwsgj` 提供 **38 个 CLI 子命令**，根目录 **307 个可导入文件**（305 个域模块 + 2 个入口）。实时数量以 `jwsgj.__all__` 与 `python -m jwsgj --help` 为准。场景标签：#skill-audit #doc-score #security-audit #refactor-acceptance #delivery-gate #dead-code #false-positive #pipeline。与 skill-creator 配合时仅参考其规范；页面交互类任务移交 browser。

## 何时使用

| 应当触发                                          | 不应触发                       |
| --------------------------------------------- | -------------------------- |
| 创建、整理、体检、评分、诊断、审计、重构或清理 AgentSkill / Python 项目 | 只做业务功能、非代码成品或一般业务咨询        |
| SKILL.md 全读、提炼整合去重、文档提分与重排、description 路由与触发覆盖优化 | 无源码且无法取得治理证据的黑盒任务          |
| 安全审计、调用链断裂、死代码、架构共存、覆盖率、日志埋点、误报交叉验证与归零排查     | 数据库运维、部署发布、权限外操作           |
| 批量管线推进、进度恢复、AI 审核、交付门禁、基线验收与复盘反哺             | 把只读诊断、方案或预演当成写盘授权          |
| 技能体检打分、技能为何不被路由、技能重叠、打包与版本提升                | 主要产出为文档排版、页面交互或写实图片的创作任务   |

**强词登记表是唯一事实源**：`diag_types_vocab.MANDATORY_PIPELINE_TRIGGER_KEYWORDS`，共 13 个词——`bug`、`缺陷`、`扇出`、`测试`、`诊断`、`治疗`、`验证`、`审计`、`分析`、`检查`、`优化`、`死代码`、`清理`。大小写不敏感，任一命中即进入完整管线；否定语境只能拦截非强制词，不能拦截强词。

| 层  | 约束                                          | 实现入口                                                                                                                |
| -- | ------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| 入口 | 强词登记与否定语境契约不满足时返回 `error`                   | `match_pipeline_trigger` / `probe_pipeline_trigger` / `jwsgj.build_text_scoring.validate_pipeline_trigger_contract` |
| 管线 | 默认 `full=True`；AI 审核停批点自动批量审核后接续            | `run_pipeline_from_trigger(..., full=True)`                                                                         |
| 门禁 | 要求契约通过、已执行、完整管线，并到达放行相位                     | `jwsgj.diag_zero_backlog_gate.check_trigger_enforcement`                                                            |

- **英文同义**：skill review、code review、static analysis、safety audit 与中文说法同等触发。

- **对象**：技能目录、`SKILL.md` 或项目根；只贴 BUG 日志、覆盖率数字或无法运行的代码片段时，同样按治理意图处理。

- **意图**：区分只读诊断与写盘执行；方案、预演与清理建议不自动获得写盘权限。

- **开关**：`full=False` / `--single-step` 只做单步诊断；`--allow-soft` 放行弱词或模糊近义命中；`--force` 接管 `miss` 并隐含 `--execute`，须配 `--skill`。

- **留痕**：触发记录写入 `runtime_paths.get_temp_dir(skill_dir)` 下的 `trigger_enforcement.json`，不写入被治理技能根。

```python
import jwsgj

# 强词命中后推进完整管线，并回读相位与归零计数。
try:
    result = jwsgj.run_pipeline_from_trigger(
        "这个 BUG 必须跑完整管线", skill_dir, full=True)
    print(result["status"], result["data"]["phase"])
    progress = jwsgj.get_pipeline_progress(skill_dir)
    print(progress["phase"], jwsgj.check_zero_backlog(skill_dir)["backlog_count"])
except RuntimeError as exc:
    print("管线中断，改用单步：", exc)
```

## 快速上手（Quick Start）

前提条件：Python ≥ 3.10（`pyproject.toml` 的 `requires-python`）。运行时依赖 `PyYAML`（frontmatter/工作流解析）、`psutil`（内存与资源画像）、`tomli`（仅 Python < 3.11）、`z3-solver`（符号执行通道，缺失降级 AST 近似）、`coverage`（覆盖率采集）、`pytest`（测试执行）；测试与 lint 链另含 `pytest-xdist`、`pytest-rerunfailures`、`ruff`，`packaging` 仅在版本/依赖规格比较时使用。frontmatter 的 `dependencies.packages.pip` 与 `requirements.txt` 同步（后者为 SSOT）。首次导入自动补装运行依赖，`JWSGJ_SKIP_DEPS=1` 关闭自举；`deps --check` 与 `deps --install` 互斥。

- **自举一次**：首次 `import jwsgj` 会按 `diag_self_check` 的映射表补齐缺失依赖，之后不再重复检测；离线环境先跑 `deps --check` 确认缺口。

- **评分只读**：`diag_skill_doc` 不写盘，可随时重跑；只产方案须显式 `auto_apply=False`，否则直接覆盖源文档。

```bash
python -m jwsgj deps --check      # 只检测，不安装
python -m jwsgj deps --install    # 检测并补装缺失依赖
```

| 目标       | 调用                                                                                        |
| -------- | ----------------------------------------------------------------------------------------- |
| 轻量代码诊断   | `python -m jwsgj light-diag <项目根> --json -o <report.json>`                                |
| 文档评分     | `jwsgj.diag_skill_doc(<SKILL.md 路径>)`                                                       |
| 保存方案不改源  | `jwsgj.refactor_skill_doc(<SKILL.md 路径>, output_path=<方案路径>, auto_apply=False)`             |
| 采纳方案并复检  | `jwsgj.apply_refactored_doc(<SKILL.md 路径>, proposal_path=<方案路径>)`                         |
| 推进 / 查询管线 | `jwsgj.run_pipeline_batch(<技能目录>, max_steps=200)` / `jwsgj.get_pipeline_progress(<技能目录>)` |
| 原话触发完整管线 | `jwsgj.run_pipeline_from_trigger(<原话>, <技能目录>, full=True)`                                 |

```python
from pathlib import Path

import jwsgj

skill_dir = Path("C:/path/to/my-skill").resolve()
md_path = str(skill_dir / "SKILL.md")
if not Path(md_path).is_file():
    raise FileNotFoundError(md_path)

# 先评分，再生成「不自动采纳」的重构方案。
try:
    report = jwsgj.diag_skill_doc(md_path)
    print(report.overall_score, report.overall_grade)
    plan = jwsgj.refactor_skill_doc(
        md_path,
        output_path=str(skill_dir.parent / "SKILL.refactored.md"),
        auto_apply=False,
    )
    print(plan["status"], plan["output_path"], plan["estimated_score"])
except RuntimeError as exc:
    print("评分为只读操作，失败即停：", exc)
```

## 入口归属与导入

未标模块前缀的入口可从 `jwsgj` 包级导入；带 `jwsgj.<module>.` 的入口必须写完整模块路径，不要假定它也在 `jwsgj.__all__` 中。返回值可能是 `dict`、dataclass 或报告对象，按签名取字段并处理异常。需要按域定位入口时，详见 [模块索引](references/module-index.md) 文末。

| 意图      | 入口                                                                                                                                                                                          | 产出                    |
| ------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------- |
| 技能创建与发现 | `build_preflight`、`run_guided_creation`、`quick_match_skills`、`detect_skill_overlaps`                                                                                                          | 预检、骨架、匹配与重叠检测         |
| 体检与生命周期 | `diag_skill`、`jwsgj.build_skill_health.run_five_dimension_health`、`maint_health_check`、`run_health`                                                                                           | 健康、僵尸、生命周期管理与运行体征     |
| 文档治理    | `diag_skill_doc`、`refactor_skill_doc`、`apply_refactored_doc`、`get_standard_sections`                                                                                                          | 评分、方案、采纳与章节注册表        |
| 代码与调用链  | `jwsgj.diag_method_invoke.run_single_method`、`jwsgj.diag_file_scanner.quick_scan`                                                                                                             | 单方法 A–F 诊断与文件扫描        |
| 安全与运行时  | `diag_skill_security`、`run_security_analysis`、`run_a3_silent_degrade`                                                                                                                         | 安全、模拟运行异常与静默退化证据      |
| 拓扑与边界   | `scan_boundary_imports`、`jwsgj.diag_module_topology.build_module_topology`                                                                                                                     | 拓扑、非法导入与循环依赖          |
| 清理与共存   | `run_deadcode_cleanup`、`cross_validate_deadcode`、`scan_stubs`、`quick_cleanup`、`quick_coexistence_scan`、`quick_arch_coexistence_scan`                                                            | 预演、复核、待审清理与共存分析       |
| 清理裁决    | `apply_cleanup_fix(skill_dir, plan_id, fixed_source, description="")`、`reject_cleanup_plan(skill_dir, plan_id, reason="")`                                                                    | 执行或驳回已审核计划            |
| 重构与治疗   | `run_refactor_workflow(skill_dir, dry_run=True)`、`run_refactor_execution`、`jwsgj.build_refactor_policy.check_refactoring_discipline`                                                            | 重构工作流与纪律检查            |
| 基线与验收   | `jwsgj.build_refactor_gate.capture_baseline`、`jwsgj.build_refactor_gate.save_baseline`、`jwsgj.build_refactor_gate.check_acceptance`                                                              | 快照、持久化、六项验收与回滚裁决      |
| 测试与日志   | `jwsgj.diag_coverage_scan.scan_test_coverage`、`profile_test_performance`、`analyze_test_coverage`、`run_targeted_regression`、`audit_log_coverage`、`analyze_log_patterns`、`check_log_quality`      | 覆盖率、慢用例、回归、埋点与日志质量    |
| 缺陷扇出    | `run_fanout_diagnosis`、`scan_signatures`、`select_fanout_strategy`、`build_fanout_findings`、`fanout_residual_gate`、`summarize_fanout_strategies`                                                  | 签名、同族位点、策略与残留门禁       |
| AI 审核   | `list_pending_ai_reviews`、`run_next_ai_review`、`run_all_ai_reviews`、`apply_ai_fix`、`apply_ai_fix_batch`、`set_ai_review_provider`                                                                | 待审队列、逐条/批量审核、修复执行与提供方 |
| 误报与归零   | `jwsgj.diag_zero_backlog_gate.audit_fp_mask`、`fixate_fp_rules`、`jwsgj.diag_zero_backlog_gate.check_zero_backlog`、`check_precision_gate`                                                        | 误报复核、固化、精确证据与归零       |
| 管线推进    | `run_pipeline_batch`、`run_next_pipeline_step`、`run_pipeline_from_trigger`、`get_pipeline_progress`                                                                                                 | 批量/单步推进与恢复            |
| 复盘与反哺   | `run_fupan`、`quick_analyze`、`run_retrospective`、`run_feedback_loop`、`run_log_driven_evolution`、`jwsgj.diag_delivery_integrity_gate.record_memory_injection`                                     | 复盘、反馈、规则沉淀与记忆回执       |
| 写前预防    | `inject_full_prevention_prompt`、`aaf_verify_hallucination_precheck`、`get_entry_guard`                                                                                                          | 预防提示、幻觉预检与写前门禁        |
| 报告与查询   | `generate_html_report`、`jwsgj.build_discover_sixdim.describe_script_layout`、`list_diag_series`、`get_series_rule_ids`                                                                              | HTML、脚本布局与规则查询         |

```python
import jwsgj
from jwsgj.build_refactor_gate import check_acceptance
from jwsgj.diag_coverage_scan import scan_test_coverage

# 包级入口与模块级入口混用时，按上表的导入归属取值。
print(jwsgj.get_pipeline_progress(skill_dir))
try:
    coverage = scan_test_coverage(skill_dir)
    print(coverage["status"], coverage["data"]["totals"]["percent"])
    baseline = jwsgj.build_refactor_gate.capture_baseline(str(skill_dir))
    print(check_acceptance(str(skill_dir), baseline, auto_rollback=False))
except RuntimeError as exc:
    print("扫描失败：", exc)
```

- **导入归属**以本表为准：带 `jwsgj.<module>.` 前缀的入口只在模块级提供，其余可从包级导入。

- **同步义务**：模块增删后同步更新 `skill_profile.json` 与 [模块索引](references/module-index.md)（需要核对域归属时查看），再运行 `diag_skill_doc` 检查陈旧引用。

- **写盘与产物**约束详见「关键约束」章节，不要在本节推断默认参数。

## 治理管线

按阶段1、阶段2a/2b、G、阶段3a/3b、阶段4/4b、阶段5、阶段6a～6e 推进，遵循诊断 → 修复 → 回归验证；通过预演、备份、回滚与迭代收敛保障安全。阶段说明：阶段1 只读取证，2a/2b 交叉验证同一批 finding，G 做同族扇出，3a/3b 出可回滚方案，4/4b 治疗与 AI 审核交替，5 复盘，6a～6c 反哺规则与代码，6d 落漏报探针基线，6e 做进化审核后才允许交付。`pipeline_steps_phases._PNS_PHASE_CHAIN` 定义 16 个相位：

| 阶段              | 相位（按推进顺序）                                             | 推进入口                                            |
| --------------- | ----------------------------------------------------- | ----------------------------------------------- |
| 1 诊断            | `pending_diagnosis` → `diagnosis_done`                  | `run_diagnosis_step`                            |
| 2a / 2b 交叉验证    | `cv_regression_done` → `cv_main_done`                   | `run_regression_cv_step` → `run_cv_step`        |
| G 扇出            | `fanout_done`                                           | `run_dry_route_step`                            |
| 3a / 3b 方案      | `plan_dry_done` → `plan_generated`                      | `run_treatment_plan_step`                       |
| 4 / 4b 治疗与审核    | `treatment_done` → `ai_fix_pending` → `ai_fix_done`     | `run_treatment_step` → `run_ai_manual_fix_step` |
| 5 复盘            | `review_done`                                           | `run_stage5_review` / `run_review_step`         |
| 6a / 6b / 6c 反哺 | `fupan_done` → `feedback_done` → `code_feedback_done`   | `run_fupan_step` → `run_feedback_loop_step` → `run_code_feedback_step` |
| 6e 进化审核         | `evolution_pending`                                     | `run_auto_enhance_step`                         |
| 终态              | `all_completed`                                         | —                                               |

```python
import jwsgj

# 批量推进前预热缓存，停批后按 next_action 续跑。
try:
    jwsgj.get_warmed_cache(skill_dir)
    batch = jwsgj.run_pipeline_batch(skill_dir, max_steps=200)
    print(batch["status"], batch["phase"], batch["next_action"])
    print(batch["progress"]["completed"], batch["progress"]["total"])
except RuntimeError as exc:
    print("批量中断，改用单步：", exc, jwsgj.run_next_pipeline_step(skill_dir))
```

- **单步失败**停留当前相位；`status="early_stopped"` 表示 AI 审核、反哺介入、步数上限或锁占用，按 `next_action` 调 `run_next_ai_review` 或 `run_next_pipeline_step`。

- **停批原因**：`stopped_reason` 以 `blocked:` 开头表示锁被占用，`ai_review_pending` 表示停批待审核；`run_pipeline_from_trigger(..., execute=False)` 只探测，`execute=True`（默认）才推进。

- **父进程绑定**：`PipelineGuard.enter` 安装父进程死亡看门狗（Windows `OpenProcess` + `WaitForSingleObject`，POSIX `os.getppid` + `kill` 轮询）；会话 shell 退出或被杀后，管线在一个轮询周期内自行终止，不留孤儿进程。

## 全严重度归零门禁（P0–P3 强制）

`apply_delivery_gates` 按下表**执行顺序**串行裁决九道门禁（2a 精确证据守卫内嵌于零残留守卫），任一未过即阻断：

| #  | 门禁        | 判据                                                                                                                                                    | 入口                               |
| -- | --------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------- |
| 0  | 方法可达性     | 注册表里的诊断方法必须能被枚举并进入 `next_method`；不可达即硬阻断——否则完整管线静默跳过该方法，「没发现」反而放行                                                                                   | `check_method_reachability`      |
| 1  | 归零门禁      | 当前轮全部 finding 有终态证据；台账轮次登记完整；`finding` 总量 ≥ 20 且株连式模糊终态占比 > 50% 时阻断                                                                                   | `check_zero_backlog`             |
| 2  | 零残留守卫     | 无 deferred/rejected/suggestion 软销项；`fp_confirmed` 规则已进 `fp_rules.json`；已声明修复不得复现；内嵌 2a 精确证据守卫裁决                                                        | `check_zero_residual`            |
| 2a | 精确证据（内嵌）  | **P0–P3 全部**：终态必须有逐项精确证据（台账 `finding_id` 级、治疗终态三元组、locator/path 精确裁决）；rule_id/basename 株连式模糊裁决记残留；P0 只接受 `fixed/ai_fixed/succeeded` 真实修复 | `check_precision_evidence`       |
| 3  | 诊断全量入账    | 反向枚举本轮诊断阶段报告（诊断 A–F）的全部 finding，要求每条都在台账 `finding_seen` 中登记；**P0–P3 全严重度**缺一即阻断——堵住「聚合/交叉验证静默丢弃 = 没发现」的掩盖路径                                | `check_diagnosis_ledger_coverage` |
| 4  | 阶段报告配对    | `htm` 阶段 HTML 与 `zhenduan` 同名快照一一对应：缺配套 JSON、条目数不一致、快照结构非法、本技能孤儿快照均阻断；无归属的历史遗留只提示迁移                                                         | `check_stage_pair_integrity`     |
| 5  | 复盘记忆注入质量  | 阶段 6a 复盘质量分 ≥ 60、记忆操作非空、每条操作都有 `jinhua/memory_injection_receipt.jsonl` 注入回执（path + content 指纹）；accuracy 维度同时受误报率与漏报率约束，`fp_rate` 与 `fn_rate` 均无样本时封顶 70 分；精度样本不可读（`precision_sample_state=unreadable`）时阻断 | `check_memory_injection_quality` |
| 6  | 漏报探针      | 注入内置 26 个缺陷模板 + AI 已审核激活的历史缺陷模板；`fn_probe_history` 最近一轮漏报率 ≤ 20%，且无规则在无缺陷对照样本上误报（`precision_violation` 直接否决激活）；首轮只记基线，无探针记录时中性跳过                            | `check_false_negative_probe`     |
| 7  | 精度趋势      | 误报率与漏报率最近 3 轮不得连续上升 ≥ 5 个百分点；连续退步说明反哺在反向生效，须停住定位根因；同时暴露退休态规则清单                                                                                   | `check_precision_trend`          |
| 8  | 触发强制管线    | 触发记录满足 `contract_passed=true`、`executed=true`、`full_pipeline=true`，且相位到达放行集；无触发记录时中性跳过（`skipped=true`）                                                  | `check_trigger_enforcement`      |

```python
import jwsgj

# 九道门禁串行裁决；任一返回 passed=False 即阻断，next_action 给出修复路径。
try:
    out = jwsgj.run_auto_enhance_step(skill_dir)
    print(out["status"], out["next_action"])
    gates = jwsgj.diag_zero_backlog_gate.apply_delivery_gates(skill_dir, out)
    print(gates, jwsgj.check_zero_backlog(skill_dir)["backlog_count"])
except RuntimeError as exc:
    print("门禁执行异常，保守阻塞：", exc)
```

- **治疗项只有两条合法出口**：`fixed/ai_fixed/succeeded`（真实修复）或 `fp_confirmed`（附 `fp_evidence` 并完成误报规则固化）。`suggestion` 不再是终态（`SOFT_CLOSURE_BANNED_STATUSES`），reject/defer 被拒绝后条目保持 `pending`；CV uncertain 复核 `defer` 同样不是终态。

- **每轮会话结束必须自动复盘**：`run_fupan_step` 产出质量分与记忆操作 → `record_memory_injection` 写入注入回执 → 交付门禁核验「复盘内容已注入灵犀记忆系统」。

- **异常一律保守阻塞**：门禁异常不得当作放行信号；`backlog_count=-1` / `memory_ops_count=-1` / `pair_violation_count=-1` / `survived_count=-1` 为异常哨兵。

- **漏报探针**由阶段 6d 的 `_run_fn_probe_baseline` 每轮落基线（`run_cached_false_negative_probe` → `fn_probe_history`），否则 5/6 会永远停在 `skipped`。探针结果按技能指纹缓存（源码与 `SKILL.md` 内容 + 已激活历史模板内容的 SHA-256，刻意不用 `evolution_state` 的 mtime——探针每轮都会写历史，用 mtime 会导致缓存永不命中），内容未变不重跑，避免每轮 6 秒开销与向 `DetectorRegistry` 重复注册 26 条固化规则；`check_memory_injection_quality` 在无样本时惰性补跑一次，探针异常暴露为 `precision_sample_state=unreadable` 保守阻塞。

- **规则退休**：`rule_retirement_state` 按累计样本量与误报占比判定——样本 ≥ 50 且误报占比 ≥ 60%、确认占比 < 20% 时判定退休；**退休规则直接不产出 finding**（`assemble_xv_result` 返回 `None`），因为 `suggestion` 在 `SOFT_CLOSURE_BANNED_STATUSES` 里，产出来会让 `check_zero_residual` 永久阻断交付（死锁）。可见性由 `retired_rule_ids` — 即退休规则清单，用 `retired_suppression_stats` 查跳过计数 — 保证，真问题回潮时自动解除。

- **历史缺陷模板（半自动，不自动激活）**：`collect_probe_template_candidates` 从 `fixed/ai_fixed/succeeded` 且带备份的 finding 生成「修复前/后」成对样本，写入 `probe_template_candidates` 并标 `pending_review`；无备份条目只留摘录并标 `needs_manual_sample`。激活必须由 AI 审核后显式调 `register_probe_template`——校验 `rule_id` 已固化、`sample_source` 可 AST 解析，通过后写 `probe_templates` 并回写候选为 `approved`。模板总数 = 内置 26 + 历史激活（上限 30）；缓存指纹含 `evolution_state` mtime，注册后自动失效。

- **抑制标签反向污染防护**：CV 自动抑制（rule4 安全阀）未经 `audit_fp_mask` 复核时只记中性 hit（不记 `fp`、不记 `confirmed`，证据族/信号通道同样跳过），避免错误抑制自我强化；真正的负样本由 `fixate_fp_rules` 在复核通过后回写（返回 `negative_samples_recorded`）。`get_adaptive_threshold` — 自适应阈值入口，在 `fp<=0 且 confirmed<=0` 时不做调整；`unreviewed_suppression_stats()` 可查未复核抑制欠账。

- **阶段报告配对门禁**以 `stage_pair_status` 为唯一判据：阻断时状态为 `stage_pair_blocked`、`next_action=repair_stage_pairs`。

- **放行相位**为 `code_feedback_done`、`evolution_pending`、`all_completed`；全管线执行中的新鲜 `running` 记录可临时放行，终态仍由 `all_completed` 复核。

- **另一套「八门禁」不可替代**：`diag_delivery_gate` 提供 GATE-01 架构容量、02 功能完整性、03 导入链完整性、04 空桩比率、05 子系统存在性、06 文件大小、07 完整导入验证、08 反碎片，由 `delivery-gate` 子命令驱动。

## 能力全景

jwsgj 是面向 AgentSkill 与 Python 代码库的全链路治理内核，工作流固定为「确认对象与授权 → 只读诊断 → 复核证据 → 生成方案 → 取得授权 → 写盘执行 → 回归验证与门禁推进」，只读取证与写盘执行严格分离。

- **技能治理侧**：能创建预检、生成骨架与文档初稿、做可发现性六维发现与优化、跨技能语义匹配与重叠检测、打包校验与版本提升，能出健康画像与评分、识别僵尸技能，也能对 SKILL.md 做五维评分、description 路由与触发覆盖审计、整合去重、重构采纳与评分回归，并挖掘触发词表、评估触发激活效果，还能给出修复引导知识、识别规则身份、划定修复边界并在修复后校验。
- **代码诊断侧**：覆盖文件与 AST 扫描、共享分析底座、调用图还原与隐式调用识别、断裂点判定、四层盲区、反模式与代码坏味、技术债度量、复杂度与大函数分解、内聚度与历史演进、异常传播与并发分析、数据层画像、符号完整性与表面一致性、文档与代码一致性、告警质量、增量代码审查，并给出十维综合评分。
- **安全侧**：覆盖注入、污点追踪、路径穿越、XSS、SSTI、反序列化、导入安全与导入时间守卫、SQL 连接与语句守卫、符号执行与 Concolic 约束求解。
- **架构侧**：检查依赖拓扑、循环依赖、跨层导入、模块边界与架构规则族（单一职责、薄门面、分层方向、类与协议、表达式、IO 控制、循环、作用域绑定），并做架构共存与新旧实现识别、合并安全判定。
- **清理侧**：处理死代码、兼容桩、残留、文件卫生与备份生命周期。
- **测试运行侧**：做 xdist 安全的全量覆盖率采集与缺口清单、慢用例定位与性能剖析、变异测试、定向回归、测试导入审计与套件编排、运行时守卫的安装快照与状态查询、沙箱模拟、业务链活性验证、资源泄漏、静默退化、日志埋点与静默通道、日志模式分析。
- **重构治疗侧**：提供治疗计划与状态机、证据裁决与经验沉淀、治疗反馈、重构预演、拆分规划与预算估算、大函数分解、源码重写、迁移准备与提交、迁移诚实度评估、重构防退化六约束、API 契约基线、六项验收与自动回滚，以及受控安全写盘。
- **扇出与交叉验证**：发现缺陷后，按同族签名做扇出扫描，一次找齐全库同类位点并完成策略选择、残留门禁与治疗交接；再经证据通道、交叉复核、证据强度、置信度复核、仲裁与阈值学习完成交叉验证，把误报固化成规则并登记归零台账。
- **门禁与审核**：所有结论都要通过归零门禁、精确证据守卫、零残留守卫、五道交付门禁与八项硬门禁，中间穿插 AI 审核队列的条目通道、条目计划与逐条批量判定，写盘前执行预防规则注入（参数、容器、流程、作用域、字面量、语言质量）、代码引用校验与幻觉预检。
- **复盘与产物**：最后自动复盘质量评分、核验消费链、协调并分级反馈，经日志驱动进化沉淀为记忆桥与注入回执，反哺下一轮；产物侧可生成 HTML 诊断报告、管线报告与审核报告，并提供脚本合规生成、Agent 模板、固化引擎、依赖治理、自检与断点续跑。

## 域总览

根目录共 307 个 `.py` 文件：**305 个域模块 + 2 个入口**（`__init__.py`、`__main__.py`，计入域 1），按 17 个能力域归类、每个文件只出现一次；`tests/` 不计入模块清单。文件清单与 225 个包级入口函数详见 [模块索引](references/module-index.md)（需要逐文件核对时查看）。

| 域         | 模块数 | 职责                            |
| --------- | --- | ----------------------------- |
| 运行底座与公开面  | 12  | 包级导出、CLI 运行时、路径缓存、日志与技能画像（含 2 个入口） |
| 管线编排      | 8   | 相位推进、文本触发、批次调度、进度恢复、报告装配与交付追溯 |
| 诊断内核      | 116 | 文件/AST/调用图/盲区/安全/污点/评分/门禁/台账  |
| 六域引擎 A–F  | 15  | 质量、内聚与历史、安全、符号执行、变异与死代码       |
| 交叉验证      | 14  | 证据通道、置信度、仲裁、阈值学习与误报过滤         |
| 预防规则与代码引用 | 19  | 规则 ID、代码引用、写前检查与预防提示          |
| 构建与生成     | 40  | 创建预检、发现匹配、模板/脚本、文档重写、拆分与安全写盘  |
| 技能治理与修复   | 12  | 文档诊断/渲染/重构守卫、审计规则与扫描内核        |
| 治疗与重构     | 14  | 治疗状态/证据、源码重写、迁移、验收与 API 契约    |
| 复盘与反馈     | 7   | 复盘分析、质量评分、消费链、反馈协调与留痕         |
| 反哺与记忆     | 5   | 日志驱动进化、记忆桥、反馈与操作生成            |
| 测试与覆盖率    | 18  | 覆盖率、静态/运行时分析、变异、性能与测试套件       |
| 清理与共存     | 7   | 死代码/残留/文件卫生、新旧实现与架构共存         |
| 报告渲染      | 5   | 诊断/管线/审核报告与 HTML 构件           |
| AI 审核     | 5   | 待审队列、条目通道、条目计划、治理判定与执行        |
| 幻觉防护      | 3   | 写前规范、台账与幻觉预检                  |
| 扇出与反馈     | 7   | 同族缺陷、代码反馈、误报判定与日志模式           |

```python
import jwsgj

# 查询诊断系列、规则 ID 与标准章节注册表。
try:
    series = jwsgj.list_diag_series()
    print(len(jwsgj.__all__), series)
    print(jwsgj.get_series_rule_ids("security"))
    print(jwsgj.get_standard_sections()[:2])
except RuntimeError as exc:
    print("查询失败：", exc)
```

- **前缀约定**：`diag_*` 取证、`engine_*` 执行、`xv_*` 复核、`build_*` 构建、`treatment_*` 治疗、`refactor_*` 改写、`html_*` 交付、`ai_review_*` 审核、`retrospective_*` 沉淀。

- **完整文件名按需到模块索引加载**，不在本文件穷举——穷举文件树会触发 L4 穷举惩罚与上传密度检查。

- **规范校验**：新增模块先按 AgentSkills 规范校验目录与 frontmatter，再更新 `skill_profile.json` 的 `layer_map`（306 条，`__init__` 由 `domain_prefixes` 登记）。

## 典型应用场景

| 场景     | 推荐顺序                                                                                                         | 产出             |
| ------ | ------------------------------------------------------------------------------------------------------------ | -------------- |
| 技能创建   | `build_preflight()` → `run_guided_creation()` → `diag_skill_doc()`                                           | 预检、骨架、重叠检测与创建后评分 |
| 文档提分   | `diag_skill_doc()` → `refactor_skill_doc(md_path, auto_apply=False)` → 审阅采纳 → `check_acceptance()` 复检       | 方案与评分回归证据      |
| 安全与扇出  | `diag_skill_security()` → `run_fanout_diagnosis()` → `fanout_residual_gate()`                                | 漏洞、同族位点与残留门禁   |
| 死代码与共存 | `run_deadcode_cleanup()` → `cross_validate_deadcode()` → `quick_cleanup()`                                   | 复核与待审清理项       |
| 重构验收   | `capture_baseline()` → `save_baseline()` → 预演重构 → 执行重构 → `check_acceptance()`                                | 基线、六项指标与裁决     |
| 测试与日志  | `scan_test_coverage()` → `profile_test_performance()` → `run_targeted_regression()` → `audit_log_coverage()` | 覆盖缺口、慢用例、回归与埋点 |
| 误报收敛   | `audit_fp_mask()` → `fixate_fp_rules()` → `check_zero_backlog()`                                             | 复核、固化与归零结论     |
| 全链路治理  | `get_warmed_cache()` → `run_pipeline_batch()` → AI 审核 → `get_pipeline_progress()`                            | 相位、待审项与恢复策略    |

```bash
python -m jwsgj light-diag ./project --json -o ./report.json
python -m jwsgj delivery-gate ./project --baseline ./baseline.json --ci
```

- **场景顺序**：箭头表示调用先后，不必逐项执行；门禁未过时先修阻断项，再进入下一场景。

- **CLI 与 API 分工**：CLI 适合单点扫描与 CI，API 适合组合流程；表中简写以「入口归属与导入」为准。

- **六项验收**：`check_acceptance` 的 cycles、illegal_imports、public_api、complexity、tests、merge_decisions 六项指标全部 `pass` 才结项。


## 脚本清单（CLI）

`python -m jwsgj <子命令> [参数]` 共 38 个子命令；退出码 `0` 通过、`1` 阻断、`2` 使用错误。参数与 `--json` 支持情况以各命令 `--help` 为准。

| 分类      | 子命令                                                                                                                                   | 用途                     |
| ------- | ------------------------------------------------------------------------------------------------------------------------------------- | ---------------------- |
| 技能生命周期  | `init`、`package`、`validate`、`bump-version`                                                                                            | 建骨架、打包、校验与版本提升         |
| 综合诊断    | `diag`、`light-diag`、`call-chain`、`blindspot-scan`、`biz-chain`、`runtime-analysis`                                                      | 评分、轻量诊断、调用链、盲区、业务链与运行时 |
| 安全      | `security`、`concolic`、`import-check`                                                                                                  | 污点漏洞、约束求解与导入安全         |
| 覆盖率与守卫  | `coverage-scan`、`guard-install`、`guard-snapshot`、`guard-status`                                                                       | 覆盖率、运行时守卫与快照           |
| 重构与交付   | `split-plan`、`estimate-splits`、`refactor-guard`、`assess-migration`、`contract`、`incremental-review`、`delivery-gate`、`fanout`           | 拆分、迁移、契约、审查、门禁与扇出      |
| 生成与固化   | `agent-template`、`solidify`、`stub-scan`                                                                                               | Agent 模板、规则固化与兼容桩      |
| 可发现性与维护 | `optimize`、`arch-rules`、`audit-patterns`、`log-coverage`、`memory-enhance`、`trigger`、`trigger-mine`、`prune-backups`、`self-check`、`deps` | 优化、规则、日志、记忆、触发、备份、自检与依赖 |

```bash
python -m jwsgj --help                    # 查看全部 38 个子命令
python -m jwsgj self-check --json         # 门面可导入性与依赖自检
```

- **依赖子命令**：`deps --check` 与 `deps --install` 互斥，前者只报告缺口。

- **CI 退出码**：`delivery-gate`、`refactor-guard`、`assess-migration` 用退出码 `0/1/2` 驱动流水线，`1` 即阻断合并。

- **触发子命令**：`trigger` 强命中后默认推进完整管线，`trigger-mine` 从 `log/trigger_events.jsonl` 挖掘新词建议。

## 用户示例

- 全读技能根目录文件，提炼、整合、去重 SKILL.md，并按代码行为更正文档。
- 保留并扩充 description，检查技能路由会不会漏选。
- 帮我给这个技能做个体检并打分；看看哪些技能长期没人用。
- 帮我创建一个新技能并先做预检；诊断下 SKILL.md 并给出提分方案。
- 审阅后采纳文档重构并回归评分；更正文档中的过时文件名、失效入口和错误默认参数。
- 查查项目的调用链断在哪里；分析下依赖拓扑、循环依赖和跨层导入。
- 做一次安全审计，排查注入、污点和路径穿越；审计日志覆盖、静默通道和静默退化。
- 找出死代码和兼容桩，只给清理方案，不删除；检查模块的架构共存与兼容桩风险。
- 重构先预演，完成后做六项验收；评估这次重构能不能通过六项验收与交付门禁。
- 跑一下覆盖率并定位慢用例；跑一遍测试、检查扇出、验证修复，然后给出归零结论。
- 复核误报并检查归零门禁；帮我固化误报规则，避免同类问题重复出现。
- 这个 BUG 从诊断一路跑到反哺进化，不要停在单步。
- 帮我把这个技能的目录结构整理一下，把长文档拆到 references/。
- 检查一下 SKILL.md 是不是太长了，帮我压缩到能一次读完。
- 这个技能为什么总是不被触发？帮我审计 description 和触发覆盖。
- 对比两个版本的代码，看看哪些业务功能在重构中丢了。
- 把这次诊断的结论复盘一下，沉淀成规则和记忆。
- 提交前帮我跑一遍交付门禁，CI 里也要能阻断。
- 这个模块的扇出影响面有多大？同族位点都找出来。
- 帮我把过时的兼容桩清掉，先给方案，我确认后再动手。

## 目录结构与账本

根目录共 307 个可导入 `.py` 文件，含 305 个域模块与 2 个入口；账本集中在 `jinhua/`，运行态与报告由 `runtime_paths` 归口。

```text
jwsgj/
├── SKILL.md                        能力、入口、约束与场景
├── references/module-index.md      307 个可导入文件 + 225 个包级入口函数的分域清单
├── __init__.py / __main__.py       326 个包级导出与 38 个 CLI 子命令
├── 305 个域模块 .py                 17 个能力域
├── tests/                          回归测试目录（按 test_<module>.py 命名，不计入模块清单）
├── pyproject.toml / requirements.txt
├── skill_profile.json              域前缀、layer_map（306 条）与已知债务
├── log/                            技能主日志与 trigger_events.jsonl
└── jinhua/                         反哺进化（固定产物集，单一账本）
```

`jinhua/` 的产物集由 `EVOLUTION_ROOT_ARTIFACTS`（`evolution_state.json`、`evolution_events.jsonl`、`retrospective_report.json`、`lifecycle_state/` 与 `EVOLUTION_AUX_ARTIFACTS` 登记的 17 个具名账本）固定枚举，全部平铺在 `jinhua/` 根下。反哺进化跨目标通用：本包自身、外部技能与 Python 项目共用同一套账本，**不按治理目标新建子目录**。`scan_unregistered_jinhua_dirs` 扫描未登记目录，`scan_unregistered_jinhua_artifacts` 扫描未登记文件，任何未登记项判为残留；新增产物必须先登记 `ArtifactSpec`。

账本共用，**项目内相对定位键必须带项目作用域**：`path_scoped_namespace(root)`（`<目录名>-<8 位路径哈希>`）。已覆盖四处：`_human_confirmations.json` 的 `project` 字段与缓存键、`cv_conclusion_history.jsonl` 的 `project` 字段、`zero_backlog_ledger.jsonl` 的 `finding_id` 与 `round_open.project`、`growth_history` 的 `project_path` 过滤。新增跨轮匹配账本时同样处理，否则 A 项目的结论会在 B 项目同名相对路径上误抑制真问题。门禁入口：`check_locator_scope_integrity`（只报告缺 `project` 的条目，不把整份账本当可删残留）。

共享账本的**读-改-写必须全程持有 `locked_artifact(path)`**：`_human_confirmations.json`、`cv_conclusion_history.jsonl`、`evidence_weights.json` 均已在锁内重读磁盘再合并写，避免两个治理会话并发时后写者用旧快照覆盖前者。`threading.RLock` 只防进程内重入，不代替跨进程锁。

**审计流水的统一保留契约**：可以「压缩」，不可以「静默丢弃」；一旦必须丢弃，就要让门禁变红。

| 产物                          | 保留口径                 | 硬上界                               | 溢出行为                                              |
| --------------------------- | -------------------- | --------------------------------- | ------------------------------------------------- |
| `evolution_events.jsonl`    | 最近 20 轮 + 灰数据 200 条  | `EVOLUTION_EVENTS_MAX_BYTES` = 4MB | 轮次让位字节（`_retain_recent_rounds` → `prune_jsonl_file`） |
| `zero_backlog_ledger.jsonl` | 3 轮 + 单条 `carry_snapshot` | `_MAX_CARRIED_FINDINGS` = 500 条   | **门禁阻断**（`carry_overflow > 0`）                      |
| `ai_review_verdicts.jsonl`  | 4MB 字节               | `_VERDICTS_JSONL_MAX_BYTES` = 4MB  | 尾部保留 2/3                                          |
| `cv_conclusion_history.jsonl` | 20 轮                 | `OSCILLATION_HISTORY_KEEP` = 20    | 尾部保留                                              |

**`evolution_events.jsonl` 的双层保留**：消费者 `_round_receipts` 按轮次精确匹配，单一字节判据会在单轮超大时把前几轮全裁掉。`_retain_recent_rounds` 先按轮次留最近 20 轮（当前轮即使滑出窗口也强制保留）、灰数据只留最近 200 条，再由 `prune_jsonl_file` 按字节兜底。写入侧 `record_memory_injection` 在轮次锚缺失时**拒绝写入**；`evolution_events_stats` 提供只读健康度查询。

**`zero_backlog_ledger.jsonl` 的快照化**：`carry_forward` 是「未复核 finding 跨轮追踪」的唯一载体，丢弃即静默漏报。`prune_ledger` 把逐条结转事件收敛为**每轮一条** `carry_snapshot`（`findings` 数组只保留 `_FINDING_STATE_KEYS` + `finding_id` + `origin_round`，事件数 O(finding) → O(1)）；超过 `_MAX_CARRIED_FINDINGS` 时按最旧截断并记 `overflow_count`，门禁见 `carry_overflow > 0` **直接阻断**。`carried_findings` 同时展开 `carry_snapshot.findings` 与存量 `carry_forward`（向后兼容）。

**`ai_review_verdicts.jsonl` 的分级摘要**：`review_target_digest` 是留痕体积主因（`provenance` + `fix_plan` + `code_context` 占 86%）。`_digest_for_verdict_log` 做**两级降级**：一级逐字段摘要（字段名全留、字符串截 256 字符、嵌套 dict 在 2 层内保留 12 键），二级只留标量核心 + 键清单。目的是保留「审核时 AI 看了哪些依据」的可追溯骨架，同时让单条体积可预测；不要改回「全有或全无」的断崖式降级。

## 关键约束

### 调用与写盘

- **参数**：文档三入口收 `SKILL.md` 路径，项目扫描收根目录；`scan_signatures`、`build_fanout_findings`、`generate_html_report` 按签名收报告或数据对象。

- **报告命名**：阶段报告统一走「中文语义名 + 17 位时间戳」（年月日时分秒毫秒），HTML 落 `htm/`、配套 JSON 落 `zhenduan/` 且与 HTML 同 stem（`诊断A20261121104830438.html` / `.json`）。六个诊断方法固定为 `诊断A`～`诊断F`，其后依次为 `扇出G`、`交叉验证`、`审核治疗`、`复盘反哺`、`最终报告`；同一轮次共用同一个时间戳便于关联。旧英文前缀（`diag_stage_`、`cv_report_`、`stage_fanout_`、`stage_treat_review_`、`stage_retro_feedback_`、`final_report_`）仅作只读兼容。

- **资源声明**：`build_preflight` 的 `resources` 仅接受 `scripts`、`references`、`assets`、`tests`（`diag_types_vocab.ALLOWED_RESOURCES`）；非法或未知类型会使 `ensure_valid_structure` 返回失败、`check_structure` 抛 `ContractViolationError`，且阻断发生在任何写盘之前。

- **默认值**：`run_deadcode_cleanup`、`run_refactor_execution`、`run_refactor_workflow`、`quick_cleanup`、`quick_coexistence_scan` 默认 `dry_run=True`；`refactor_skill_doc` 默认 `auto_apply=True`；`build_preflight` 默认 `write_back=False`；`run_guided_creation` 默认 `dry_run=False`。

- **文档写回**：只产方案须显式 `auto_apply=False`，方案仍写入 `output_path`（省略时由 `resolve_proposal_path` 选择受控落点）。`apply_refactored_doc` 默认 `verify=True`，先备份再写回；方案与源文件同内容时按幂等返回（`status="ok"`、`applied=False`，不重写、不产生备份）；评分回退超过 `REGRESSION_THRESHOLD`（0.01）时自动恢复。所有文档写回入口共用 `<工作空间>/Temp/_backups/apply_md/<源文档哈希>/` 分片备份根，每个源文档各自保留 5 份；写盘失败源文件保持原样。`refactor_skill_doc` 把运行期异常收敛为结构化 `status`/`detail`；参数类型等前置校验失败仍会直接抛出，调用方需 try/except。

- **进化守卫**：`evolution_guard` 固定包含 `regression_detected`、`rolled_back`、`rollback_failed`；回滚失败时 `rollback_failed=True` 且源文件停留已写状态，须从 `backup_path` 人工恢复。

- **缓存**：`run_pipeline_batch`、`run_next_pipeline_step`、`jwsgj.diag_method_invoke.run_single_method` 自动预热；`run_a3_silent_degrade`、`diag_regression_guard` 等引擎入口要求传入已预热的 `cache`，否则抛 `jwsgj.shared_cache.CacheNotWarmedError`。

- **清理**：`quick_cleanup` 只分析并送 AI 审核；执行用 `apply_cleanup_fix`，驳回用 `reject_cleanup_plan`。删除前解析绝对路径与影响，优先回收站或备份，禁止对根目录或未验证变量递归删除。

- **基线**：`capture_baseline` 只取快照，`save_baseline` 才写入 `jinhua/`。`check_acceptance` 默认 `test_status="not_run"`、`auto_rollback=True`；须传真实测试结果，纯评估传 `auto_rollback=False`，仅在提供 `rollback_id` 且验收失败时才可能回滚。

- **入口归属**：`fixate_fp_rules`、`check_zero_backlog`、`apply_cleanup_fix`、`reject_cleanup_plan` 有包级入口；`audit_fp_mask`、`check_zero_residual`、`check_precision_evidence` 只从 `jwsgj.diag_zero_backlog_gate` 导入；`capture_baseline`、`save_baseline`、`check_acceptance`、`scan_test_coverage` 只在模块级。数据库读写须参数化，动态 SQL 片段须白名单校验。

```python
import jwsgj
from jwsgj.build_refactor_gate import capture_baseline, check_acceptance, save_baseline

# 传入真实测试结果；纯评估禁用自动回滚。
try:
    baseline = capture_baseline(str(skill_dir))
    save_baseline(str(skill_dir), baseline)
    verdict = check_acceptance(
        str(skill_dir), baseline, test_status="passed", auto_rollback=False,
    )
    print(verdict["status"], jwsgj.get_pipeline_progress(skill_dir)["phase"])
except RuntimeError as exc:
    print("验收流程中断：", exc)
```

### 评分口径

| 阶段             | 权重  | 关注点                      |
| -------------- | --- | ------------------------ |
| 匹配 matching    | 20% | description、双语、口语近义词与角色视角 |
| 捕捉 capture     | 15% | 章节、深度、结构、模块、语义与参数文档      |
| 加载 loading     | 15% | 资源、文件结构、API、文件树与函数描述     |
| 内容 content     | 30% | 示例、边界、签名、代码-API 对齐与场景映射  |
| 上传 upload      | 20% | YAML 与内容限制合规             |

等级：≥90 A、≥75 B、≥60 C、≥40 D。另有 10 分维度惩罚：任一子维度低于 30 分时按项扣 10 分。C9 源码 docstring 语义覆盖与 C6 参数注释来自源码扫描，仅改 `SKILL.md` 无法消除；L4 在提供统计摘要时按实现上限计 80 分，完整清单详见 `references/module-index.md`（需要逐文件核对时查看），避免穷举文件树反被扣分。`keywords` / `dependencies` 是 jwsgj 扩展字段：`diag_self_check.DependencySpec`、匹配诊断、六维生成器与发现索引仍按顶层读取，故 `UV-002` 记为已知债务；迁移到 `metadata` 须同步改这些读取侧。

## 设计原则

- **先证后改、只读优先**：发现可复现，证据不足只留待办；诊断不改目标源码。

- **账本驱动**：发现、裁决、治疗与反哺留痕，门禁看终态而非口头结论。

- **分层解耦**：`diag_*` 取证、`xv_*` 复核、`treatment_*` 治疗、`retrospective_*` 沉淀。

- **收敛可恢复**：无新增证据即停批，基线、验收、备份与回滚形成闭环。

- **降级留痕、幂等落盘**：可选检查失败可降级但须记日志；重复执行不产重复产物，路径由 `runtime_paths` 归口。

- **权限最小化**：默认只读与预演，写盘、删除和回滚分别核对授权、目标与影响。

## 陷阱（Gotchas）

- frontmatter 必须从文件第一行 `---` 开始并以 `---` 结束；`version` 需与 `pyproject.toml`、`jwsgj.__version__` 三方对齐；`description` 上限 1024 字符（`diag_types_vocab.DESC_MAX`），超限触发 UV-010（high，扣 20 分），不会静默截断。

- `skill_profile.json` 的 `layer_map` 是权威层表，覆盖全部 306 个模块名（`__init__` 由 `domain_prefixes` 登记）；未登记模块回落到启发式分层，可能产生假的层次违规。

- `diag_method_invoke` 的 `_engine_a` / `_engine_b` / `_engine_d` / `_engine_e` / `_engine_f` 为函数级 import 的延迟加载（无 `_engine_c`，C 通道在 `_log_engine_c_run` 内联）；改动前核对 `CohesionAnalyzer.cycle_exempt_lazy_edges`，避免顶层循环依赖。

- 结果带 `source_changed_during_run` 时源码指纹已变化，结论不可采信，须复跑。

- `diagnostic_read_scope` 是只读诊断作用域，在 `memoize_walk=True` 时持有线程绑定的进程级 RLock；`run_dimension_channels` 按维度通道并行检查，启动方持锁后 `join` 已进入该通道的 worker 会死锁，应把作用域下移到 worker，如 `diag_method_invoke._run_worker` 的 `scope_kwargs`。

- `get_temp_dir(skill_dir)` 解析技能隔离的运行态根目录（`<工作空间>/Temp`），相对路径按历史契约先归一为绝对路径；无可用工作空间时抛 `RuntimeError` 而非静默兜底。

# jwsgj

[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Python](https://img.shields.io/badge/python-3.10%2B-blue.svg)](pyproject.toml)

jwsgj 是面向 AgentSkill 与 Python 代码库的全链路治理内核，工作流固定为「确认对象与授权 → 只读诊断 → 复核证据 → 生成方案 → 取得授权 → 写盘执行 → 回归验证与门禁推进」，只读取证与写盘执行严格分离。

技能治理侧能创建预检、生成骨架与文档初稿、做可发现性六维发现与优化、跨技能语义匹配与重叠检测、打包校验与版本提升，能出健康画像与评分、识别僵尸技能，也能对 SKILL.md 做五维评分、description 路由与触发覆盖审计、整合去重、重构采纳与评分回归，并挖掘触发词表、评估触发激活效果，还能给出修复引导知识、识别规则身份、划定修复边界并在修复后校验。

代码诊断侧覆盖文件与 AST 扫描、共享分析底座、调用图还原与隐式调用识别、断裂点判定、四层盲区、反模式与代码坏味、技术债度量、复杂度与大函数分解、内聚度与历史演进、异常传播与并发分析、数据层画像、符号完整性与表面一致性、文档与代码一致性、告警质量、增量代码审查，并给出十维综合评分；安全侧覆盖注入、污点追踪、路径穿越、XSS、SSTI、反序列化、导入安全与导入时间守卫、SQL 连接与语句守卫、符号执行与 Concolic 约束求解；架构侧检查依赖拓扑、循环依赖、跨层导入、模块边界与架构规则族（单一职责、薄门面、分层方向、类与协议、表达式、IO 控制、循环、作用域绑定），并做架构共存与新旧实现识别、合并安全判定；清理侧处理死代码、兼容桩、残留、文件卫生与备份生命周期；测试运行侧做 xdist 安全的全量覆盖率采集与缺口清单、慢用例定位与性能剖析、变异测试、定向回归、测试导入审计与套件编排、运行时守卫的安装快照与状态查询、沙箱模拟、业务链活性验证、资源泄漏、静默退化、日志埋点与静默通道、日志模式分析；重构治疗侧提供治疗计划与状态机、证据裁决与经验沉淀、治疗反馈、重构预演、拆分规划与预算估算、大函数分解、源码重写、迁移准备与提交、迁移诚实度评估、重构防退化六约束、API 契约基线、六项验收与自动回滚，以及受控安全写盘。

发现缺陷后，按同族签名做扇出扫描，一次找齐全库同类位点并完成策略选择、残留门禁与治疗交接；再经证据通道、交叉复核、证据强度、置信度复核、仲裁与阈值学习完成交叉验证，把误报固化成规则并登记归零台账。

所有结论都要通过归零门禁、精确证据守卫、零残留守卫、五道交付门禁与八项硬门禁，中间穿插 AI 审核队列的条目通道、条目计划与逐条批量判定，写盘前执行预防规则注入（参数、容器、流程、作用域、字面量、语言质量）、代码引用校验与幻觉预检。最后自动复盘质量评分、核验消费链、协调并分级反馈，经日志驱动进化沉淀为记忆桥与注入回执，反哺下一轮；产物侧可生成 HTML 诊断报告、管线报告与审核报告，并提供脚本合规生成、Agent 模板、固化引擎、依赖治理、自检与断点续跑。

> 脚本只产发现、方案与建议；代码修改由 AI 审核后亲自执行，且必须是根因修复。

## 特性

- **38 个子命令**：覆盖诊断、安全、重构、交付门禁、运行时守卫、技能生命周期
- **307 个模块，111 个门面全部可导入**（`jwsgj self-check` 可复验）
- **依赖可降级**：缺少可选依赖时按映射表逐包补装或降级，不整链崩溃
- **零配置起步**：不依赖数据库、不依赖网络，标准库优先
- **可作为 AgentSkill 加载**：`SKILL.md` 随包安装，支持技能式调用

## 安装

要求 **Python ≥ 3.10**。

```bash
# 方式一：从 GitHub 直接安装
pip install git+https://github.com/flavor-my/jwsgj.git

# 方式二：克隆后本地安装
git clone https://github.com/flavor-my/jwsgj.git
cd jwsgj
pip install .

# 方式三：不安装，直接运行
git clone https://github.com/flavor-my/jwsgj.git
cd jwsgj
pip install -r requirements.txt
python -m jwsgj --help
```

安装完成后即可使用 `jwsgj` 命令（等价于 `python -m jwsgj`）。

### 作为 AgentSkill 使用

把整个仓库目录放进宿主技能目录，`SKILL.md` 位于仓库根目录，无需额外配置：

```
<skills-dir>/jwsgj/
├── SKILL.md          # 技能入口文档
├── __init__.py
├── __main__.py
└── ...
```

## 快速开始

```bash
jwsgj --help                 # 查看全部 38 个子命令
jwsgj self-check             # 自健康检查：门面导入 / Python 版本 / 依赖
jwsgj deps --check           # 只检测依赖，不安装
jwsgj deps --install         # 检测缺失并定向补装

jwsgj security ./src         # 安全漏洞扫描（污点追踪 / 注入 / XSS / SSTI / 反序列化）
jwsgj light-diag ./src       # 轻量一键诊断（调用链 + 反模式 + 十维评分）
jwsgj arch-rules             # 查看 11 条内置架构规则
```

## 命令总览

### 诊断与体检

| 命令 | 说明 |
|---|---|
| `diag` | 代码诊断（增强版，需技能目录结构） |
| `light-diag` | 轻量一键诊断：调用链 + 反模式 + 十维评分总览 |
| `call-chain` | 调用链诊断：构建调用图 + 断裂点 + 判定 |
| `blindspot-scan` | 四层盲区扫描（脚本 / 模块 / 函数 / 代码） |
| `biz-chain` | 业务链运行诊断：入口点 → 调用链 → 模拟执行 → 活性验证 |
| `runtime-analysis` | 运行时分析：沙箱模拟 + 资源泄漏 / 异常分析 |
| `security` | 安全漏洞扫描：污点追踪 / 注入 / XSS / SSTI / 反序列化 |
| `fanout` | 缺陷扇出诊断：种子签名 + 全库同族位点 + 残留门禁 |
| `import-check` | 导入安全检查：四维扫描 + 导入链完整性验证 |
| `arch-rules` | 内置架构规则目录查询（ARCH-* 11 条） |
| `audit-patterns` | 审计模式快速检查 |
| `coverage-scan` | 测试覆盖率实测扫描（xdist 安全采集 + 缺口清单） |
| `log-coverage` | 日志覆盖度审计（埋点 / 运行时暴露 / 静默通道三层） |
| `incremental-review` | 增量代码审查：变更文件四步审查 + 回归风险评分 |
| `concolic` | Concolic 导向探索：分支路径约束 + 具体测试输入生成 |

### 重构与交付门禁

| 命令 | 说明 |
|---|---|
| `refactor-guard` | 重构防退化守护（六约束检查，退出码 0/1/2） |
| `assess-migration` | 迁移诚实度评估 + 六约束纪律门禁 |
| `split-plan` | 拆分规划报告（评分 / 边界 / 风险 / 步骤 / 回滚，只读不改码） |
| `estimate-splits` | 生成前拆分预算协商（大纲 → 行数预估 → 拆分建议） |
| `delivery-gate` | 交付前硬门禁（CI 退出码 0/1/2） |
| `contract` | INFRA 底座契约基线（capture 抓基线 / check 复检） |

### 技能生命周期

| 命令 | 说明 |
|---|---|
| `init` | 初始化新技能目录 |
| `package` | 打包技能为 `.skill` 文件 |
| `validate` | 校验技能目录 |
| `optimize` | 可发现性优化 |
| `bump-version` | 版本提升（SKILL.md 同步 + 历史落盘） |
| `agent-template` | Agent 友好模板生成（生成即合规） |
| `solidify` | 固化引擎：待固化点分析 / 规则清单 / 模式挖掘建议 |
| `stub-scan` | 兼容桩 / 门户文件存量盘点 |
| `trigger` | 管线触发探测（三层漏斗） |
| `trigger-mine` | 触发留痕词表挖掘 |
| `memory-enhance` | 管线报告记忆增强 |

### 运行时守卫与维护

| 命令 | 说明 |
|---|---|
| `guard-install` | 安装运行时守卫（覆盖率采集 + 异常捕获钩子） |
| `guard-snapshot` | 保存运行时守卫覆盖率快照 + 异常摘要 |
| `guard-status` | 查看运行时守卫运行状态 |
| `prune-backups` | 备份根生命周期清理（默认预览） |
| `deps` | 依赖治理：第三方包 / 测试工具链 / 外部工具检测与补装 |
| `self-check` | 技能包自健康检查 |

## 依赖

| 包 | 用途 | 缺失行为 |
|---|---|---|
| `PyYAML` | 配置与 frontmatter 解析 | 降级 |
| `psutil` | 运行时资源观测 | 降级 |
| `z3-solver` | 符号执行与约束求解 | 相关命令不可用 |
| `coverage` | 覆盖率采集 | 覆盖率相关命令不可用 |
| `pytest` | 回归执行 | 测试相关命令不可用 |
| `tomli` | Python < 3.11 的 TOML 解析 | 仅 3.10 需要 |

`git` 为系统级外部工具（回归 CV 依赖），不在 pip 范围，由 `deps` 命令检测并提示。

## 项目结构

```
.
├── SKILL.md                 # AgentSkill 入口文档
├── __init__.py              # 门面导出
├── __main__.py              # CLI 入口（38 个子命令）
├── diag_*.py                # 诊断引擎（调用链/污点/盲区/测试/安全）
├── build_*.py               # 构建与门禁（重构/契约/技能质量）
├── prevention_*.py          # 预防性检查规则
├── engine_*.py              # 多引擎编排（A/B/D/E/F 系列）
├── xv_*.py                  # 交叉验证（证据/仲裁/置信度）
├── treatment_*.py           # 治疗规划与反馈
├── refactor_*.py            # 重构执行
├── skill_*.py               # SKILL.md 文档处理
├── cleanup_*.py             # 清理与残留治理
├── testsuite_*.py           # 测试编排
├── html_*.py                # HTML 报告渲染
└── references/              # 模块索引等参考文档
```

## 开发

```bash
pip install -r requirements.txt
pytest                      # 回归测试
ruff check .                # 静态检查
```

## 许可证

[Apache License 2.0](LICENSE)，含专利授权条款。使用时请保留 `LICENSE` 与版权声明；修改文件需保留变更说明。

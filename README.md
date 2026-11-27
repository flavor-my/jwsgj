# jwsgj

[![License: Apache-2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Python](https://img.shields.io/badge/python-3.10%2B-blue.svg)](pyproject.toml)

Python 代码与 AgentSkills 的全链路治理工作流，把治理串成六阶段闭环：

> 诊断 → 交叉验证 → 治疗规划 → AI 审核执行 → 复盘 → 反哺

每轮都是「诊断 → 修复 → 验证」的收敛过程。脚本只产发现、方案与建议；代码修改由 AI 审核后亲自执行，且必须是根因修复。

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

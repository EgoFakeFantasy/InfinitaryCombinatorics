# R0：迹集、替换与非 fin-intersecting AD / MAD 族

本目录形式化论文 *Traces and replacements in non-fin-intersecting almost disjoint families*（Haoxuan Ye，2026-09-19）的数学结果。完整入口为 [Paper.lean](Paper.lean)；旧最小规模接口保留在 [Main.lean](Main.lean)。

- 非 FI 的无限 AD 族在自然数上的最小规模为分裂数 s；可实现的规模恰为闭区间 [s,c]。
- 统一构造自然数上规模恰为连续统 c 的非 FI MAD 族，对应原 Question 4.6 的不分基数情形的构造要求；最小规模结果对应 Question 4.9。
- 证明精确迹集实现、局部替换、正交类及扩张费用不变性、可数 AD 完备化、局部到整体费用界、可数交叠转移、放置公式与迹集分裂替换。
- 验证显式二进制编码及三角形附录。

**Question 4.10 仍未解决。** 规模为 a 的非 FI MAD 扩张需要文中明确列出的可数交叠或费用条件；迹集分裂替换需要一个预先固定、对所有无限指标集有效的赋值。仓库没有把这些条件加入为公理。

## 证明导航

见 [论文—定理对应表及语义审查](PAPER_COVERAGE.md)，其中列出每条数学结论、入口及实现差异。

| 模块 | 内容 |
| --- | --- |
| [Main](Main.lean) | 原 R0 下界、最小值达到及最小元 |
| [BinaryCoding](BinaryCoding.lean)、[Selectors](Selectors.lean)、[TraceRealization](TraceRealization.lean) | 显式大端二进制编码、逐块选择、精确迹集实现 |
| [Spectrum](Spectrum.lean) | 规模谱 [s,c] |
| [Local](Local.lean)、[BinarySplitting](BinarySplitting.lean) | Zorn 扩张、局部替换、有限分裂、迹集判据及障碍 |
| [Remainder](Remainder.lean)、[BranchComparison](BranchComparison.lean) | 实际最小扩张余族、费用及分支比较 |
| [UniformMAD](UniformMAD.lean) | 规模 c 的统一非 FI MAD 构造 |
| [CountableParts](CountableParts.lean)、[CountableCompletion](CountableCompletion.lean) | 有限差异配对、实际基数 a、可数族完备化 |
| [LocalGlobal](LocalGlobal.lean)、[CountableTransfer](CountableTransfer.lean)、[Placement](Placement.lean) | 费用界、保持原集合的转移、精确放置公式 |
| [Triangle](Triangle.lean)、[Consequences](Consequences.lean) | 三角形显式构造、首个不同位阈值、单点块障碍 |

`R0.lean` 与 `R0/*.lean` 是原始兼容快照，由 [源哈希清单](../../docs/r0-source-hashes.json) 固定，全部保持原字节不变。扩展全部写入本目录；基础库不反向依赖应用。

## 验证

工具链为 `leanprover/lean4:v4.30.0`，mathlib 锁定于 `c5ea00351c28e24afc9f0f84379aa41082b1188f`。运行：

```text
lake exe cache get
pwsh -File verify.ps1
```

`verify.ps1` 执行完整构建、使用示例、展开的主陈述检查、所有模块的入口覆盖、原 R0 快照哈希、禁止构造及空白检查，并审计全部项目声明的传递公理依赖。只允许 `propext`、`Classical.choice`、`Quot.sound`。

- [GitHub 自动验证](https://github.com/EgoFakeFantasy/InfinitaryCombinatorics/actions/workflows/lean.yml)
- [当前本地验收清单与源哈希](../../verification/manifest.json)
- [展开陈述检查](../../CheckFormalizations.lean)
- [全声明公理审计](../../Audit.lean)及[日志](../../verification/axiom-audit.log)

CI 对推送版本重新运行相同验收并保存证据附件。验证链接须与具体提交对应；浮动分支页面本身不是成功验证的证据。

## 语义及来源

`ADFamily` 允许有限或空的局部族；`R0.AlmostDisjoint` 与 `MAD` 要求无限的族。所有 AD 成员均无限。`MaximalOn` 允许有限局部极大家族。正交类包括有限集合，扩张费用允许零及有限值，并证明最小值实际达到。FI 删除有限的限制迹后，对每个非空有限子族要求无限交。

论文的文献来源为 Corral–Rodrigues, *Fin-intersecting MAD families*, Filomat 38(7) (2024), 2563–2578，DOI [10.2298/FIL2407563C](https://doi.org/10.2298/FIL2407563C)。相对余族观点参考 Fuchino–Geschke–Guzmán–Soukup, *How to drive our families mad*。

Rodrigues 于 2026 年 9 月告知作者，他此前已借助 GPT-5.6-Sol 获得相同最小规模结论及相近的未发表证明；本项目不主张优先于该观察，其沟通不构成对本文或扩展结果的核验或背书。

核心论证及初始 Lean 证明由 GPT-6 Astra 生成；本次扩展由 Codex 根据完整论文生成并通过 Lean 内核验收。Haoxuan Ye 提出问题、协调研究并承担论文责任。自动形式验证不等同于独立人类同行审稿，也不认证文献优先权。

# 无穷组合 Lean 基础库

这是面向所附问题登记表的第一版可复用工具库。数学基础采用经典 Lean 4 + mathlib；各模块中的 theorem/lemma 均提供完整证明。研究问题本身不作为公理加入，也不以定义包装为已解决结果。

## 问题形式化项目

[Formalizations/](Formalizations/README.md) 专门收录基于本仓库基础工具完成的无穷组合相关问题形式化，按问题分别提供证明入口、来源和验收说明。

首个收录项目为 [R0：非 FI AD 族的最小规模等于分裂数](Formalizations/R0/README.md)。该目录的 [Main.lean](Formalizations/R0/Main.lean) 复用本库内已有的完整 R0 证明；原 `R0.*` 接口保持不变。其原始本地证明先于本库完成，本次接入不主张新数学结果。

```lean
import Formalizations.R0.Main
```

`lake build` 同时构建基础库与已收录项目。基础库使用者仍可只导入 `InfinitaryCombinatorics`；应用层的展开陈述由 `CheckFormalizations.lean` 检查，并纳入统一公理审计。

## 使用

Lean `4.30.0`，mathlib `v4.30.0`；精确依赖见 `lean-toolchain` 与 `lake-manifest.json`。

公开仓库：[EgoFakeFantasy/InfinitaryCombinatorics](https://github.com/EgoFakeFantasy/InfinitaryCombinatorics)。克隆后安装 `lean-toolchain` 指定的工具链，再运行 `lake exe cache get` 与 `lake build`。

```lean
import InfinitaryCombinatorics
open InfinitaryCombinatorics
```

也可只导入下表中的具体模块，避免不必要的依赖。在另一个相邻 Lake 项目中，可先在 `lakefile.toml` 加入本地依赖：

```toml
[[require]]
name = "infinitaryCombinatorics"
path = "../infinitary-combinatorics"
```

然后运行 `lake update`，即可使用相同的 import。调整路径时应指向包含本库 `lakefile.toml` 的目录。

已有工具链时，在本目录运行：

```text
lake build
lake env lean Examples.lean
lake env lean CheckR0.lean
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

运行 `./package.ps1` 可将通过验收且哈希未变化的版本打成源码包；脚本拒绝未审计的新模块，并逐文件核对压缩包内容。

Windows 的 `./verify.ps1` 会完成构建、消费端示例、展开后的 R0 陈述、公理审计、缺口扫描、源文件导入覆盖检查，并在 `verification/` 保存带源文件哈希的报告。新环境先运行 `lake update`、`lake exe cache get`；本机通过目录联接共享 mathlib 缓存，源代码包不依赖相邻工程。

## 模块与已证工具

| 模块（均在 InfinitaryCombinatorics/） | 可复用内容 | 对应问题 |
|---|---|---|
| AlmostContainment | 模有限包含的传递、交封闭、无限性传递；与最终包含等价 | A7、A8、B1 |
| Ideal | 一般 AD 族、生成理想、MAD、nowhere MAD；理想封闭性、MAD 极大性等价、无限 AD 理想适当性 | A7、A8、B1 |
| FinIntersection | FI 的子族封闭、非 FI 的向上保持、两个不交无限迹的阻碍准则 | A7、A8、R0 |
| Transport | FI 与无限 AD 的双射不变性；跨底集编码复用 | A7、A8、R0 |
| CountableSplitting、Characteristics | 可数族的不分裂对角集；ℵ₁ ≤ s ≤ c；任意可数集合族都是 FI | A7、A8、R0 |
| PairColoring | 对称无序对染色、单色团、颜色图；拉回；新顶点扩张和覆盖条件的等价 | A2、A3、A4 |
| Delta | 任意良序坐标上的首次分歧；存在、唯一、对称、三角不等式；二叉三分支限制 | A2 |
| DisjointType | 两个等长递增集的交错类型、补类型、精确最小深度、序嵌入实现 | A1 |
| OrdinalFramework | ω 梯列、有限集的统一尾界、C 序列、类型猜测、club/驻集接口、HM/回归不可染色 | A1、A3 |
| Directed | 简单有向圈、无短圈、无圈、二色染色；诱导限制保持性和颜色纤维刻画 | A6 |
| StrongColoring | 任意序型块的两两不交族、分离矩形、Pr₁ 见证；满射重着色、块界单调性 | A5 |
| Partition | 基数版对分割关系、基数色数；无限单色集产生有限团；共尾数鸽巢原理 | A2–A6 |
| Separability | 正有限集族、SS、almost strongly separable；容易方向和非 FI 的 MAD 扩张保持 | A7、A8、B1 |

`R0/` 是已有 R0 工程的逐字源码快照，保留原有 `R0.*` 接口。包含分裂数的最小值实现、二叉树构造、嵌入搬运、`#A < s → FI A` 和非 FI AD 族最小规模等于分裂数的完整证明；来源及哈希见 `docs/PROVENANCE.md`。

## 本次验收

2026-09-17 的本地验收覆盖 24 个模块（22 个基础库模块及 2 个应用模块）、365 个声明和 212 个定理常量（含 Lean 自动生成项）。完整构建、公共接口示例、R0 与应用入口的展开陈述、全声明公理审计及缺口扫描全部通过；仅依赖 `propext`、`Classical.choice`、`Quot.sound`。精确时间、源哈希和日志以 `verification/manifest.json` 为准。

WorkBuddy 通过 Agent 广场 task 16 完成 `CountableSplitting.lean`；Codex 复核、接入推论并完成整库验收。新增库保留原有 R0 工程的源文件与接口。

## 数学边界

- A1：已构造“深度恒为零、宽度无界”的类型序列，严格区分两个假设；尚未证明有界深度类型猜测。
- A2：Δ 工具适用于任意良序坐标，包括不可数坐标；尚未证明单色 K₄ 存在。
- A3–A6：已有基础对象与保持/等价定理，尚未证明 HM 回归强化、ω₁ 极大染色、pump-up 去限制或精确规模的高二色数构造。
- A7、A8、B1：MAD 扩张大小控制、无附加假设的构造、SS 存在性反向转换仍是后续研究内容。
- 当前不包含完整的 Fodor、club guessing、强迫或模型论机制，也不宣称可立即自动形式化登记表中的全部问题。

详细定义边界、后续接口和审查结果见 [语义审查](docs/SEMANTIC_REVIEW.md)；按问题找入口见 [路线图](docs/ROADMAP.md)。[Examples.lean](Examples.lean) 是实际编译的使用示例。






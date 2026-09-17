# 无穷组合 Lean 基础库

这是一个基于 Lean 4 和 mathlib 的无穷组合基础工具库，提供 almost disjoint 族、分裂、染色、交错类型、序数梯列等对象的定义与可复用定理。

## 问题形式化项目

[Formalizations/](Formalizations/README.md) 专门收录基于本仓库基础工具完成的无穷组合相关问题形式化，按问题分别提供证明入口、来源和验收说明。

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
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

运行 `./package.ps1` 可将通过验收且哈希未变化的版本打成源码包；脚本拒绝未审计的新模块，并逐文件核对压缩包内容。

Windows 的 `./verify.ps1` 会完成构建、使用示例、主定理陈述检查、公理审计、缺口扫描和模块覆盖检查，并在 `verification/` 保存带源文件哈希的报告。新环境先运行 `lake update`、`lake exe cache get`。

## 模块与已证工具

| 模块（均在 InfinitaryCombinatorics/） | 可复用内容 |
|---|---|
| AlmostContainment | 模有限包含的传递、交封闭、无限性传递；与最终包含等价 |
| Ideal | 一般 AD 族、生成理想、MAD、nowhere MAD；理想封闭性、MAD 极大性等价、无限 AD 理想适当性 |
| FinIntersection | FI 的子族封闭、非 FI 的向上保持、两个不交无限迹的阻碍准则 |
| Transport | FI 与无限 AD 的双射不变性；跨底集编码复用 |
| CountableSplitting、Characteristics | 可数族的不分裂对角集；ℵ₁ ≤ s ≤ c；任意可数集合族都是 FI |
| PairColoring | 对称无序对染色、单色团、颜色图；拉回；新顶点扩张和覆盖条件的等价 |
| Delta | 任意良序坐标上的首次分歧；存在、唯一、对称、三角不等式；二叉三分支限制 |
| DisjointType | 两个等长递增集的交错类型、补类型、精确最小深度、序嵌入实现 |
| OrdinalFramework | ω 梯列、有限集的统一尾界、C 序列、类型猜测、club/驻集接口、HM/回归不可染色 |
| Directed | 简单有向圈、无短圈、无圈、二色染色；诱导限制保持性和颜色纤维刻画 |
| StrongColoring | 任意序型块的两两不交族、分离矩形、Pr₁ 见证；满射重着色、块界单调性 |
| Partition | 基数版对分割关系、基数色数；无限单色集产生有限团；共尾数鸽巢原理 |
| Separability | 正有限集族、SS、almost strongly separable；容易方向和非 FI 的 MAD 扩张保持 |

## 本次验收

2026-09-17 的本地验收覆盖 24 个模块、365 个声明和 212 个定理常量（含 Lean 自动生成项）。完整构建、公共接口示例、主定理陈述检查、全声明公理审计及缺口扫描全部通过；仅依赖 `propext`、`Classical.choice`、`Quot.sound`。精确时间、源哈希和日志见 [验收清单](verification/manifest.json)。

定义和定理的适用条件见 [语义审查](docs/SEMANTIC_REVIEW.md)，模块入口见 [工具导航](docs/ROADMAP.md)。[Examples.lean](Examples.lean) 提供实际编译的使用示例；各问题的成果说明见 [Formalizations/](Formalizations/README.md)。






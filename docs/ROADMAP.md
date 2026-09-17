# 基础工具导航

按数学对象查找当前已实现的接口和定理。各定理的精确假设以 Lean 陈述为准。

| 工具 | 模块与接口 | 已有定理 |
|---|---|---|
| 交错类型与深度 | `DisjointType` | `depth_spec`、`depth_swap`、`Realizes.disjoint` |
| 良序坐标首次分歧 | `Branch`、`delta`、`DeltaRegressive` | `delta_spec`、`delta_symm`、`delta_triangle` |
| 梯列与序数图 | `Ladder`、`CSequence`、`HajnalMate` | `eventually_above_finite` 与 club 交保持 |
| 对染色与顶点扩张 | `PairColoring` | `triangleFree_extend_iff`、`blocksExtensions_iff` |
| 强染色见证 | `UniformDisjoint`、`Separated`、`Pr1Witness` | `Separated.disjoint`、`pr1Witness_recolor`、`pr1Witness_mono_bound` |
| 有向圈与二色染色 | `Directed` | `noShortCycles_pullback`、`isDicoloring_iff_fibers` |
| AD 族与生成理想 | `ADFamily`、`MAD`、`InIdeal` | `mad_iff_maximal`、`nowhereMAD_not_MAD` 与理想封闭性 |
| 有限交性质 | `FinIntersection`、`Transport` | 子族保持、非 FI 向上保持与双射搬运 |
| 可数不分裂与基数界 | `CountableSplitting`、`Characteristics` | `exists_unsplit_of_countable`、`aleph0_lt_splittingNumber` |
| 可分离性 | `PositiveFinFamily`、`SS`、`AlmostStronglySeparable` | `almostStronglySeparable_implies_SS` |

## 上游复用位置

- 序数、序数区间的标准小类型、序数基数：`Mathlib/SetTheory/Ordinal/Basic.lean`。`Ordinal.ToType.mk` 将 `Iio κ` 与 `κ.ToType` 连接；跨 universe 比较基数时应显式用 `Cardinal.lift`，不要把 Lean 的 universe 差异当成数学额外基数。
- 共尾数：`Mathlib/SetTheory/Cardinal/Cofinality/Basic.lean` 与 `.../Ordinal.lean`。
- Club：`Mathlib/SetTheory/Cardinal/Cofinality/Club.lean` 中 `IsClub`、`IsClub.inter`、`IsClub.sInter`。交保持有共尾数条件，应原样保留。
- 共尾数鸽巢：`Mathlib/SetTheory/Cardinal/Pigeonhole.lean` 中 `Cardinal.infinite_pigeonhole`、`infinite_pigeonhole_set`。本库的 `full_size_fiber` 保留原假设。
- 正常图染色：`Mathlib/Combinatorics/SimpleGraph/Coloring/VertexColoring.lean`。其 `chromaticNumber : ℕ∞` 不区分不同无限基数；本库通过颜色类型和基数下界定义 `HasChromaticNumber`。
- 有向图：`Mathlib/Combinatorics/Digraph/Basic.lean`。其 `Digraph` 允许自环，本库明确将自环计作长度一的有向圈。
- 序上的最小值：`Mathlib/Order/WellFounded.lean` 中 `WellFounded.min`。Δ 直接用良基最小元，不枚举有限前缀冒充不可数坐标。

## 扩展约定

基础库新文件放在 `InfinitaryCombinatorics/`，新声明进入同名 namespace，根入口增加相应 import。先写文献陈述及参数解释，再实现小引理。每个存在性假设都要在文档中标清是已证来源还是尚缺输入。优先证明适配/等价定理；不要静默改变已有定义。最终运行 `verify.ps1`，新的私有声明同样会接受公理审计。

具体问题的形式化放入 `Formalizations/<项目名>/`，并在项目文档说明结论、来源与验收方法。

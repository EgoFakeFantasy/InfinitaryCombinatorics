# 按问题使用的路线图

登记表中的 A1–A8 和 B1 是研究目标；下表右栏是尚需独立完成的数学工作，不能作为已证定理使用。

| 目标 | 当前入口 | 已有可直接调用的关键定理 | 后续主要缺口 |
|---|---|---|---|
| A1 | `DisjointType`, `Ladder`, `CSequence`, `TypeGuessing` | `depth_spec`, `depth_swap`, `Realizes.disjoint`, `eventually_above_finite`, `exists_boundedDepth_unboundedWidth` | 定义规范序数区间上的 ladder system 选择；相邻有界宽度定理；仅依赖深度的实现机制 |
| A2 | `Branch`, `delta`, `DeltaRegressive`, `PairColoring.HasClique` | `delta_spec`, `delta_symm`, `delta_triangle`, `FirstDifference.of_lt`, `binary_no_three_same_split` | 正则不可数基数上的融合/驻集论证；六条边同色的 K₄ 实现 |
| A3 | `lowerNeighbors`, `LadderLike`, `HajnalMate`, `RegressiveUncolorable` | 梯列统一尾界、驻集与 club 的交保持 | HM 图变换及其梯状性；从回归正常染色抽取原图的可数正常染色 |
| A4 | `PairColoring.TriangleFree`, `BlocksExtensions`, `extend` | `triangleFree_extend_iff`, `blocksExtensions_iff` | ω₁ 上同时无三角形并阻止全部新点扩张的构造 |
| A5 | `UniformDisjoint`, `Separated`, `RealizesRectangle`, `Pr1Witness` | `Separated.disjoint`, `pr1Witness_recolor`, `pr1Witness_mono_bound` | 按原论文逐项装配完整参数；现有 pump-up 证明；跨越共尾数约束的新引理 |
| A6 | `Directed.Cycle`, `NoShortCycles`, `IsDicoloring`, `HasDichromaticNumber` | `noShortCycles_pullback`, `isDicoloring_pullback`, `isDicoloring_iff_fibers` | 规模恰为 κ 的高二色数构造；反映或缩小不能由限制保持定理倒推 |
| A7 | `ADFamily`, `NowhereMAD`, `FinIntersecting` | 理想封闭性和适当性、`nowhereMAD_not_MAD`、FI 子族保持、双射搬运 | 同时 nowhere MAD 和 FI 且达到连续统规模的构造 |
| A8 | `MAD`, `InIdeal`, R0 的规模 s 反例 | `mad_iff_maximal`, `nonFI_mad_extension` | 规模为 a 的 MAD 扩张/改造及连续统和 a 的完整基数框架 |
| B1 | `PositiveFinFamily`, `SS`, `AlmostStronglySeparable` | `almostStronglySeparable_implies_SS` | 存在性逆向转换；不能用同一族的直接加强替代 |
| R0 | 保留的 `R0.*` | `finIntersecting_of_card_lt`, `exists_non_finIntersecting_ad_of_size_splittingNumber`, `splittingNumber_isLeast` | 无本次要求内的证明缺口；新颖性/发表状态不由 Lean 认证 |

## 上游复用位置

- 序数、序数区间的标准小类型、序数基数：`Mathlib/SetTheory/Ordinal/Basic.lean`。`Ordinal.ToType.mk` 将 `Iio κ` 与 `κ.ToType` 连接；跨 universe 比较基数时应显式用 `Cardinal.lift`，不要把 Lean 的 universe 差异当成数学额外基数。
- 共尾数：`Mathlib/SetTheory/Cardinal/Cofinality/Basic.lean` 与 `.../Ordinal.lean`。
- Club：`Mathlib/SetTheory/Cardinal/Cofinality/Club.lean` 中 `IsClub`、`IsClub.inter`、`IsClub.sInter`。交保持有共尾数条件，应原样保留。
- 共尾数鸽巢：`Mathlib/SetTheory/Cardinal/Pigeonhole.lean` 中 `Cardinal.infinite_pigeonhole`、`infinite_pigeonhole_set`。本库的 `full_size_fiber` 保留原假设。
- 正常图染色：`Mathlib/Combinatorics/SimpleGraph/Coloring/VertexColoring.lean`。其 `chromaticNumber : ℕ∞` 不区分不同无限基数；本库通过颜色类型和基数下界定义 `HasChromaticNumber`。
- 有向图：`Mathlib/Combinatorics/Digraph/Basic.lean`。其 `Digraph` 允许自环，本库明确将自环计作长度一的有向圈。
- 序上的最小值：`Mathlib/Order/WellFounded.lean` 中 `WellFounded.min`。Δ 直接用良基最小元，不枚举有限前缀冒充不可数坐标。

## 扩展约定

新文件放在 `InfinitaryCombinatorics/`，新声明进入同名 namespace，根入口增加相应 import。先写文献陈述及参数解释，再实现小引理。每个存在性假设都要在文档中标清是已证来源还是尚缺输入。优先证明适配/等价定理；不要静默改变已有定义。最终运行 `verify.ps1`，新的私有声明同样会接受公理审计。

保留 `R0/` 快照以维持兼容与来源可追溯。如果未来需要升级其中定义，应明确建立新版本或证明等价，不修改快照哈希来掩盖变化。

# A1：深度一类型猜测推出 Kunen 区间击中原则

本项目形式化配套手稿《深度一不交类型猜测与 Kunen 区间击中原则》的内部组合论证。主证明工作在实际的第一不可数序数 `omegaOne = Ordinal.omega 1` 上，复用本库的 `DisjointType`、`Realizes`、`Ladder`、`CSequence` 和 `TypeGuessing`。

## 已证明的主结论

固定 Cantor 配对

```text
π(a,b) = (a+b)(a+b+1)/2 + b,
(a_k,b_k) = π⁻¹(k),  j_k = a_k+1,  n_k = k+3,
t_k = 0^(j_k+1) 1 0^(n_k-j_k-1) 1^(n_k-1).
```

代码证明递归配对与这一闭式完全相同，以及每个 `t_k` 的深度恰为 1。

`typeGuessing_implies_hits_thin` 证明：若梯系统 `C` 猜测该固定序列，则对每个 club `D ⊆ ω₁`，存在一个非零极限序数 `β < ω₁`，使所有 `m ≥ 1` 都满足

```text
[C_β(3m), C_β(3m+3)) ∩ D ≠ ∅.
```

`thin` 同时保留严格递增性与共尾性，所以 `A_β(m) = C_β(3m)` 是实际梯系统。`typeGuessing_implies_K_thin` 给出手稿定理 5.1 的 `K(thin C)`；起始指标 1 是证明直接给出的更精确界。

此外，已证明：

- `G_implies_KA`：存在猜测固定序列的梯系统，推出 KA。
- `BDTG_implies_G`、`BDTG_implies_KA`：有界深度类型猜测全称原则推出上述存在性及 KA。
- `not_G_of_not_KA`、`not_BDTG_of_not_KA`：相应逆否结论。
- `antiColoring_on_omegaOne`：在 `¬KA` 下，对任意梯系统，构造一个定义在全部 `ω₁` 上的自然数值染色，排除固定类型及其相反类型的所有同色见证。
- `Diamond_implies_ClubGuessing`：diamond 推出整个梯包含于 club 的 club guessing，覆盖手稿引理 7.2 的内部证明。
- `KA_implies_KAomegaOne`：把梯系统取像为一个规模至多 `ℵ₁` 的集合族，覆盖手稿引理 7.4。族的成员是序型为 `ω` 的集合，使用严格递增枚举陈述击中条件。

## 语义与证明边界

`LimitBelow omegaOne` 恰为 `ω₁` 以下的非零极限序数。基础库的 `TypeGuessing` 只量化这些点上的染色；`typeGuessing_iff_allPoints` 通过零延拓证明它与原稿在全部 `ω₁` 上量化染色的约定等价。

`K` 的量词是“每个 club，存在一条梯和一个尾部起点，之后每个半开区间都击中”。`not_K_iff` 保留同一个 club 对所有梯、任意靠后的空区间的共同见证。没有把不可数目标换成有限或可数模型。

局部编号采用等价的 next-point 构造：`nextD(x)` 是 `D` 中严格大于 `x` 的最小点。每个纤维包含于一个可数初段，且是凸集；各纤维的编号通过经典选择取得。`countable_convex_partition` 证明非空纤维组成分割，编号在每个成员上单射，并将每个避开 `D` 的半开区间放进同一成员。不同分割成员允许使用相同编号；没有假设 `ω₁ → ℕ` 全局单射。该构造只用到无界性，因而适用于所有 club。

反染色依次选择空区间和避开初始点编号的间隙。形式化允许任取满足条件的见证，不要求它是最小见证；主结论不依赖最小性。初始梯点无需位于所选空区间。

**未形式化的外部输入**：手稿引用的 Lambie-Hanson–Uhrik club guessing 到类型猜测定理、Jensen 的构造宇宙 diamond 结果，以及 Asperó 的强迫和 KA 失败结果。代码没有用额外公理代替这些文献定理。这里交付的是 Lean/mathlib 中的内部组合蕴含证明，不是整个相对独立性或强迫模型构造的形式化，也不认证数学首次性。

## 手稿对应与文件导航

| 手稿部分 | 文件 | 主要入口 |
| --- | --- | --- |
| §3，式 (3.1) | [CantorPairing.lean](CantorPairing.lean) | `cantorPair_closedForm`、配对互逆与单射 |
| §3，引理 3.1 | [TypeSequence.lean](TypeSequence.lean) | `typeSeq_depth`、`typeSeq_order` |
| §2，定义及量词 | [Principles.lean](Principles.lean) | `K`、`KA`、`G`、`BDTG`、`typeGuessing_iff_allPoints` |
| §4，局部编号与两个间隙 | [LocalNumbering.lean](LocalNumbering.lean) | `localNumbering_injOn_empty`、`two_gaps` |
| 引理 4.1，完整分割陈述 | [Partition.lean](Partition.lean) | `countable_convex_partition` |
| 定理 5.1，推论 6.1/6.2 | [Main.lean](Main.lean) | `typeGuessing_implies_K_thin`、`antiColoring_on_omegaOne` |
| 引理 7.2 | [Diamond.lean](Diamond.lean) | `exists_ladder_in_set`、`accumulationPoints_isClub`、`Diamond_implies_ClubGuessing` |
| 引理 7.4 | [FamilyPrinciple.lean](FamilyPrinciple.lean) | `KA_implies_KAomegaOne` |
| 展开陈述与公理打印 | [Check.lean](Check.lean) | 全域染色、两种方向、三倍抽稀、完整 KA 否定 |

主归约只需 `import Formalizations.A1.Main`。附录可分别导入 `Formalizations.A1.Diamond` 和 `Formalizations.A1.FamilyPrinciple`；`import Formalizations` 覆盖全部证明及检查模块。

## 验收

使用仓库锁定的 Lean 4.30.0 与 mathlib 版本：

```text
lake build
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

Windows 运行 `./verify.ps1`，执行源码缺口扫描、模块覆盖、R0 快照核验、统一构建、陈述检查和传递公理审计。实际验收时间和源哈希见 [manifest.json](../../verification/manifest.json)，输出见 [构建日志](../../verification/build.log)、[陈述检查](../../verification/formalizations-statements.log) 和 [公理审计](../../verification/axiom-audit.log)。允许的公理仅 `propext`、`Classical.choice`、`Quot.sound`。

§3 的初始实现由 WorkBuddy 完成；Codex 核查后补全闭式对应、§4–§6、引理 7.2/7.4、公开说明和统一验收。基础库和原 R0 证明的数学陈述保持不变。

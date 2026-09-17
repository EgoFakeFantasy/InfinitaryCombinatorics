# R0：非 fin-intersecting AD 族的最小规模

本项目将本地已经完成的 R0 证明接入本仓库的 [问题形式化目录](../README.md)。数学结论为：非 fin-intersecting 的无限 almost disjoint 族的最小规模等于分裂数 s，并且存在底集为自然数、规模恰为 s 的见证。

## 主定理与实际证明

[Main.lean](Main.lean) 导入本仓库的 `InfinitaryCombinatorics`，在 `InfinitaryCombinatorics.Formalizations.R0` 中提供四个经内核检查的入口：

| 声明 | 结论 |
| --- | --- |
| `small_families_are_finIntersecting` | 规模小于 s 的任意集合族都是 FI；不需要 AD 假设 |
| `exists_counterexample_of_size_s` | 自然数上存在无限 AD 族，非 FI 且规模恰为 s |
| `least_counterexample_cardinal` | s 属于反例规模集合，并且是其最小元 |
| `nonFinIntersectingNumber_eq_splittingNumber` | 非 FI AD 族的最小规模等于 s |

这些入口直接使用已有完整证明，没有重新定义 AD、FI、分裂数或改变结论。原本的 `R0.*` 接口及七个快照源文件保持不变，以便基础库继续复用相关引理。

## 完整证明导航

| 共享源码 | 作用 |
| --- | --- |
| [R0/Basic.lean](../../R0/Basic.lean) | 分裂、AD、有限块、迹、中心性与 FI 的定义 |
| [R0/LowerBound.lean](../../R0/LowerBound.lean) | 不分裂的迹族产生中心化限制 |
| [R0/SplittingNumber.lean](../../R0/SplittingNumber.lean) | 分裂数的最小值实现与 FI 下界 |
| [R0/TreeConstruction.lean](../../R0/TreeConstruction.lean) | 二叉树构造、AD 性及非 FI 阻碍 |
| [R0/Transport.lean](../../R0/Transport.lean) | 将构造保真搬运到自然数 |
| [R0/Main.lean](../../R0/Main.lean) | 基数计算、最小值及最终等式 |

主入口为本库的复用示例；上表链接通向实际构造与证明体，不是未完成的外部依赖。六个模块及 `R0.lean` 的原始内容哈希由 [快照清单](../../docs/r0-source-hashes.json) 固定。

## 语义与验收

`AlmostDisjoint A` 同时要求族 A 无限、每个成员无限、不同成员相交有限。FI 先去掉有限的限制迹，再对所有非空有限子族检查无限交。最终见证确实位于自然数上，且最小规模被达到。

[CheckFormalizations.lean](../../CheckFormalizations.lean) 对新入口检查展开后的存在性、下界、最小元和等式；[CheckR0.lean](../../CheckR0.lean) 保留原接口检查。统一公理审计同时遍历基础库、旧 R0 与新应用声明，拒绝标准经典 Lean 公理之外的依赖。

```text
lake build
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

上述结论不包含保持指定基数的 MAD 扩张定理。

## 来源与贡献说明

数学问题和定义来自 Corral–Rodrigues, *Fin-intersecting MAD families*, Filomat 38(7) (2024), 2563–2578，尤其 Definition 2.3、Theorem 3.1、Proposition 4.8 与 Question 4.9。

原始 R0 论证与 Lean 形式化由 GPT-6 Astra 生成，用户提供研究问题；Codex 完成本库接入与验收。原证明先于基础库完成，其定义及中间引理已被基础库复用；本目录将它作为首个收录项目呈现。`R0.lean` 与 `R0/*.lean` 保留原始源码，并由快照哈希检查其一致性。

该记录不主张结果的历史首次性，也不等同于独立人类同行审稿。主陈述经过重新编译和展开检查；Lean 内核验证证明项，不认证文献优先权或问题的最新研究状态。基础库的定义说明见 [语义审查](../../docs/SEMANTIC_REVIEW.md)。

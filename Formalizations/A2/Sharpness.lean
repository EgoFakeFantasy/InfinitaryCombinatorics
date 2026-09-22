import Mathlib.SetTheory.Ordinal.Basic
import InfinitaryCombinatorics.Delta
import InfinitaryCombinatorics.PairColoring
import Formalizations.A2.Basic

/-! Binary first differences: no common split for three distinct branches. -/

namespace InfinitaryCombinatorics.Formalizations.A2

open Set
universe u

/-- 三个二值分支不可能两两具有相同的首差坐标。

这是手稿定理 2.3 证明中「H 至多与两个纤维相交」的核心一步。
直接复用基础库的 `binary_no_three_same_split`：二值分支在
同一坐标上只有两个取值，无法容纳三个两两不同的值。 -/
theorem no_three_same_delta {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    (x y z : ι → Bool) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hxy_eq : delta x y hxy = delta x z hxz)
    (hyz_eq : delta y z hyz = delta x z hxz) : False := by
  have h1 : FirstDifference x y (delta x z hxz) := by
    simpa [hxy_eq] using delta_spec x y hxy
  have h2 : FirstDifference y z (delta x z hxz) := by
    simpa [hyz_eq] using delta_spec y z hyz
  exact binary_no_three_same_split h1 h2 (delta_spec x z hxz)

/-- 上述结论的推论形式：给定三个分支，它们的首差坐标不可能全都相等。 -/
theorem not_all_three_delta_eq {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
    (x y z : ι → Bool) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ¬ (delta x y hxy = delta x z hxz ∧ delta y z hyz = delta x z hxz) := by
  rintro ⟨h1, h2⟩
  exact no_three_same_delta x y z hxy hyz hxz h1 h2

/-- **若染色的颜色在首差上是单射的，则不存在单色三角形。**

这是手稿第 4、5 节论证的**机制核心**，用于命题 5.3 的反例：

1. 三点 `x, y, z` 同色（颜色 `k`）；
2. 由「颜色在首差上单射」，三对的首差被迫全部相等；
3. 但 `no_three_same_delta` 排除了三个二值分支两两首差相同的可能。

因此手稿的染色必须**放弃**单射性才能容纳单色集：
定理 2.3 的染色正是把 `∆ = ω` 与 `∆ = 1` 都染成 `0`，
用这一处碰撞换取四元单色集的存在。 -/
theorem no_triangle_of_delta_injective
    {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] {K : Type*}
    (c : PairColoring (ι → Bool) K)
    (hinj : ∀ {x y u v : ι → Bool} (hxy : x ≠ y) (huv : u ≠ v),
      c.color x y = c.color u v → delta x y hxy = delta u v huv) :
    ¬ c.HasClique 3 := by
  rintro ⟨e, k, hk⟩
  let x := e (0 : Fin 3)
  let y := e (1 : Fin 3)
  let z := e (2 : Fin 3)
  have h01 : x ≠ y := e.injective.ne (by decide)
  have h12 : y ≠ z := e.injective.ne (by decide)
  have h02 : x ≠ z := e.injective.ne (by decide)
  -- 同色：由 `hk` 各自等于 `k`，转接即两点彼此相等
  have e01 : delta x y h01 = delta x z h02 :=
    hinj h01 h02 ((hk 0 1 (by decide)).trans (hk 0 2 (by decide)).symm)
  have e12 : delta y z h12 = delta x z h02 :=
    hinj h12 h02 ((hk 1 2 (by decide)).trans (hk 0 2 (by decide)).symm)
  exact no_three_same_delta x y z h01 h12 h02 e01 e12

/-- 上述结论在分支类型 `Branch κ` 上的特例。 -/
theorem no_triangle_of_delta_injective_branch {κ : Ordinal.{u}} {K : Type*}
    (c : PairColoring (Branch κ) K)
    (hinj : ∀ {x y u v : Branch κ} (hxy : x ≠ y) (huv : u ≠ v),
      c.color x y = c.color u v → delta x y hxy = delta u v huv) :
    ¬ c.HasClique 3 :=
  no_triangle_of_delta_injective c (by
    intro x y u v hxy huv h
    exact hinj hxy huv h)

end InfinitaryCombinatorics.Formalizations.A2

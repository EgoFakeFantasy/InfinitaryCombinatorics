import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Fintype.Card
import InfinitaryCombinatorics.Delta
import InfinitaryCombinatorics.PairColoring
import Formalizations.A2.Basic
import Formalizations.A2.Sharpness
import Formalizations.A2.Statements
import Formalizations.A2.Coloring

/-! Theorem 2.3: the explicit colouring has a four-clique and no five-clique. -/

namespace InfinitaryCombinatorics.Formalizations.A2

open Set
universe u

/- 坐标与便利性包装。 -/

/-- `sharpColoring` 带上显式类型，避免在下文反复写强制转换。 -/
noncomputable def sharpColoringC :
    PairColoring (Branch (Ordinal.omega0.{u} + 1)) (Set.Iio (Ordinal.omega0.{u} + 1)) :=
  sharpColoring

/-- 坐标 `1`（`1 < ω < ω+1`）。 -/
def coord1 : Set.Iio (Ordinal.omega0.{u} + 1) :=
  ⟨1, lt_trans Ordinal.one_lt_omega0 omega_lt_omega_add_one⟩

/-- `d < ω + 1` 蕴含 `d ≤ ω`（因为 `ω + 1 = succ ω`）。 -/
theorem le_omega_of_lt_omega_add_one {d : Ordinal.{u}}
    (h : d < Ordinal.omega0.{u} + 1) : d ≤ Ordinal.omega0.{u} := by
  simpa [Order.succ_eq_add_one] using (Order.lt_succ_iff).1 h

/-- `ω ≠ 0`。 -/
theorem omega0_ne_zero' : Ordinal.omega0.{u} ≠ 0 :=
  ne_of_gt (Ordinal.natCast_lt_omega0 0)

/-- `1 ≠ ω`。 -/
theorem one_ne_omega0' : (1 : Ordinal.{u}) ≠ Ordinal.omega0.{u} :=
  ne_of_lt Ordinal.one_lt_omega0

/-- 从染色取值里读出颜色值（序数形式）。 -/
theorem sharpColoring_value {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y) :
    (sharpColoringC.color x y).val = sharpColorValue hxy := by
  simp [sharpColoringC, sharpColoring, hxy]

/- 颜色值落在哪个分支：这三个引理把 `sharpColorValue` 的三段定义
   反向解读为关于首差的信息。 -/

/-- 颜色值 `= 0` 只可能来自 `∆ = 1`（`1 - 1 = 0`）或 `∆ = ω`（第三分支）。 -/
theorem sharpColorValue_eq_zero_imp {x y : Branch (Ordinal.omega0.{u} + 1)}
    (hxy : x ≠ y) (h : sharpColorValue hxy = 0) :
    (delta x y hxy).val = 1 ∨ (delta x y hxy).val = Ordinal.omega0.{u} := by
  by_cases hd0 : (delta x y hxy).val = 0
  · have hv : sharpColorValue hxy = Ordinal.omega0.{u} := by
      unfold sharpColorValue
      dsimp
      rw [if_pos hd0]
    have hz : Ordinal.omega0.{u} = 0 := hv.symm.trans h
    exact False.elim (omega0_ne_zero' hz)
  · by_cases hdω : (delta x y hxy).val < Ordinal.omega0.{u}
    · left
      have hv : sharpColorValue hxy = (delta x y hxy).val - 1 := by
        unfold sharpColorValue
        dsimp
        rw [if_neg hd0, if_pos hdω]
      have hsub : (delta x y hxy).val - 1 = 0 := by
        rw [← hv, h]
      have hdle1 : (delta x y hxy).val ≤ 1 := (Ordinal.sub_eq_zero_iff_le).1 hsub
      have hdpos : 0 < (delta x y hxy).val := by
        exact lt_of_le_of_ne bot_le (by
          intro hz
          exact hd0 hz.symm)
      have h1le : (1 : Ordinal.{u}) ≤ (delta x y hxy).val := by
        simpa [Order.succ_eq_add_one] using (Order.succ_le_iff).2 hdpos
      exact le_antisymm hdle1 h1le
    · right
      have hge : Ordinal.omega0.{u} ≤ (delta x y hxy).val := le_of_not_gt hdω
      have hle : (delta x y hxy).val ≤ Ordinal.omega0.{u} :=
        le_omega_of_lt_omega_add_one (delta x y hxy).property
      exact le_antisymm hle hge

/-- 颜色值 `= ω` 只可能来自 `∆ = 0`。 -/
theorem sharpColorValue_eq_omega_imp {x y : Branch (Ordinal.omega0.{u} + 1)}
    (hxy : x ≠ y) (h : sharpColorValue hxy = Ordinal.omega0.{u}) :
    (delta x y hxy).val = 0 := by
  by_cases hd0 : (delta x y hxy).val = 0
  · exact hd0
  · by_cases hdω : (delta x y hxy).val < Ordinal.omega0.{u}
    · have hv : sharpColorValue hxy = (delta x y hxy).val - 1 := by
        unfold sharpColorValue
        dsimp
        rw [if_neg hd0, if_pos hdω]
      have hbad : (delta x y hxy).val - 1 = Ordinal.omega0.{u} := by
        rw [← hv, h]
      have hlt : (delta x y hxy).val - 1 < Ordinal.omega0.{u} :=
        lt_of_le_of_lt (Ordinal.sub_le_self _ _) hdω
      exact False.elim ((ne_of_lt hlt) hbad)
    · have hv : sharpColorValue hxy = 0 := by
        unfold sharpColorValue
        dsimp
        rw [if_neg hd0, if_neg hdω]
      have hz : Ordinal.omega0.{u} = 0 := h.symm.trans hv
      exact False.elim (omega0_ne_zero' hz)

/-- 颜色值既不是 `0` 也不是 `ω`，则必落在中间分支：
`0 < ∆ < ω` 且颜色值 `= ∆ - 1`。 -/
theorem sharpColorValue_middle {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y)
    (h0 : sharpColorValue hxy ≠ 0) (hω : sharpColorValue hxy ≠ Ordinal.omega0.{u}) :
    0 < (delta x y hxy).val ∧ (delta x y hxy).val < Ordinal.omega0.{u} ∧
      sharpColorValue hxy = (delta x y hxy).val - 1 := by
  by_cases hd0 : (delta x y hxy).val = 0
  · have hv : sharpColorValue hxy = Ordinal.omega0.{u} := by
      unfold sharpColorValue
      dsimp
      rw [if_pos hd0]
    exact False.elim (hω hv)
  · by_cases hdω : (delta x y hxy).val < Ordinal.omega0.{u}
    · have hv : sharpColorValue hxy = (delta x y hxy).val - 1 := by
        unfold sharpColorValue
        dsimp
        rw [if_neg hd0, if_pos hdω]
      refine ⟨?_, hdω, hv⟩
      exact lt_of_le_of_ne bot_le (by
        intro hz
        exact hd0 hz.symm)
    · have hv : sharpColorValue hxy = 0 := by
        unfold sharpColorValue
        dsimp
        rw [if_neg hd0, if_neg hdω]
      exact False.elim (h0 hv)

/-- 有限段上 `d - 1 = k` 反解出 `d = k + 1`。

两侧夹逼：`k < d`（`sub_one_lt_of_lt_omega`）给出 `k + 1 ≤ d`；
`Ordinal.le_add_sub` 给出 `d ≤ 1 + (d - 1) = 1 + k`，再用
`one_add_natCast_eq_add_one` 把 `1 + k` 换成 `k + 1`（`k` 有限）。
再次强调：序数加法不交换，这一步**必须**经过自然数嵌入。 -/
theorem sub_one_eq_iff {d k : Ordinal.{u}} (hd0 : 0 < d) (hdω : d < Ordinal.omega0.{u})
    (hk : d - 1 = k) : d = k + 1 := by
  have hklt : k < d := by
    rw [← hk]
    exact sub_one_lt_of_lt_omega hd0 hdω
  have hsucc : k + 1 ≤ d := by
    simpa [Order.succ_eq_add_one] using (Order.succ_le_iff).2 hklt
  have hdle : d ≤ (1 : Ordinal.{u}) + k := by
    simpa [hk] using (Ordinal.le_add_sub d (1 : Ordinal.{u}))
  have hkω : k < Ordinal.omega0.{u} := by
    rw [← hk]
    exact lt_of_le_of_lt (Ordinal.sub_le_self d (1 : Ordinal.{u})) hdω
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hkω
  have h1k : (1 : Ordinal.{u}) + k = k + 1 := by
    rw [hn]
    exact one_add_natCast_eq_add_one n
  exact le_antisymm (by simpa [h1k] using hdle) hsucc

/-- 首差为 `ξ` 的两点必在 `ξ` 处取值不同（`FirstDifference` 的第一分量）。 -/
theorem ne_at_delta {x y : Branch (Ordinal.omega0.{u} + 1)} {hxy : x ≠ y}
    {ξ : Set.Iio (Ordinal.omega0.{u} + 1)} (hd : delta x y hxy = ξ) : x ξ ≠ y ξ := by
  have hfd : FirstDifference x y ξ := by
    simpa [hd] using delta_spec x y hxy
  exact hfd.1

/-- 首差为 `1` 时颜色值是 `0`。 -/
theorem sharpColorValue_of_delta_one {x y : Branch (Ordinal.omega0.{u} + 1)}
    {hxy : x ≠ y} (hd : delta x y hxy = coord1) : sharpColorValue hxy = 0 := by
  unfold sharpColorValue
  dsimp
  have hdval : (delta x y hxy).val = (1 : Ordinal.{u}) := by
    simpa [coord1] using congrArg Subtype.val hd
  rw [hdval]
  rw [if_neg (one_ne_zero : (1 : Ordinal.{u}) ≠ 0)]
  rw [if_pos Ordinal.one_lt_omega0]
  exact (Ordinal.sub_eq_zero_iff_le).2 le_rfl

/-- 首差为 `ω` 时颜色值是 `0`。 -/
theorem sharpColorValue_of_delta_omega {x y : Branch (Ordinal.omega0.{u} + 1)}
    {hxy : x ≠ y} (hd : delta x y hxy = omegaCoord) : sharpColorValue hxy = 0 := by
  unfold sharpColorValue
  dsimp
  have hdval : (delta x y hxy).val = Ordinal.omega0.{u} := by
    simpa [omegaCoord] using congrArg Subtype.val hd
  rw [hdval]
  rw [if_neg omega0_ne_zero']
  rw [if_neg (not_lt_of_ge le_rfl : ¬ Ordinal.omega0.{u} < Ordinal.omega0.{u})]

/- 1. 无单色五元集。 -/

/-- **定理 2.3 的第一半：`sharpColoring` 没有单色五元集。**

按颜色值 `k` 分三种情形：

- `k = 0`：`x ↦ (x(1), x(ω))` 在单色集上单射，而 `Bool × Bool` 只有 4 个点，
  与 `|Fin 5| = 5` 冲突；
- `k = ω`：所有首差为 `0`，三个点即矛盾；
- 其余 `k`：所有首差同为一个 `k + 1`，三个点即矛盾。 -/
theorem sharpColoring_noClique5 :
    ¬ (sharpColoringC : PairColoring (Branch (Ordinal.omega0.{u} + 1))
        (Set.Iio (Ordinal.omega0.{u} + 1))).HasClique 5 := by
  classical
  rintro ⟨e, k, hk⟩
  have valOf (i j : Fin 5) (hij : i ≠ j) :
      sharpColorValue (e.injective.ne hij) = k.val := by
    have h1 : (sharpColoringC.color (e i) (e j)).val = k.val :=
      congrArg Subtype.val (hk i j hij)
    exact (sharpColoring_value (e.injective.ne hij)).symm.trans h1
  by_cases hk0 : k.val = 0
  · -- 情形 k = 0：坐标对 (1, ω) 上的鸽笼
    let g : Fin 5 → Bool × Bool := fun i => (e i coord1, e i omegaCoord)
    have hg : Function.Injective g := by
      intro i j hgij
      by_contra hij
      have hxy : e i ≠ e j := e.injective.ne hij
      have hv0 : sharpColorValue hxy = 0 := by
        simpa [hk0] using valOf i j hij
      rcases sharpColorValue_eq_zero_imp hxy hv0 with hd1 | hdω
      · have hd' : delta (e i) (e j) hxy = coord1 := by
          apply Subtype.ext
          simpa [coord1] using hd1
        have hne : e i coord1 ≠ e j coord1 := ne_at_delta hd'
        have hfst : (g i).1 = (g j).1 := congrArg Prod.fst hgij
        exact hne (by simpa [g] using hfst)
      · have hd' : delta (e i) (e j) hxy = omegaCoord := by
          apply Subtype.ext
          simpa [omegaCoord] using hdω
        have hne : e i omegaCoord ≠ e j omegaCoord := ne_at_delta hd'
        have hsnd : (g i).2 = (g j).2 := congrArg Prod.snd hgij
        exact hne (by simpa [g] using hsnd)
    have hcard : Fintype.card (Fin 5) ≤ Fintype.card (Bool × Bool) :=
      Fintype.card_le_of_injective g hg
    simp at hcard
  · by_cases hkω : k.val = Ordinal.omega0.{u}
    · -- 情形 k = ω：所有首差为 0
      let x := e (0 : Fin 5)
      let y := e (1 : Fin 5)
      let z := e (2 : Fin 5)
      have h01 : x ≠ y := e.injective.ne (by decide)
      have h12 : y ≠ z := e.injective.ne (by decide)
      have h02 : x ≠ z := e.injective.ne (by decide)
      have hd01 : (delta x y h01).val = 0 :=
        sharpColorValue_eq_omega_imp h01 (by simpa [hkω] using valOf 0 1 (by decide))
      have hd12 : (delta y z h12).val = 0 :=
        sharpColorValue_eq_omega_imp h12 (by simpa [hkω] using valOf 1 2 (by decide))
      have hd02 : (delta x z h02).val = 0 :=
        sharpColorValue_eq_omega_imp h02 (by simpa [hkω] using valOf 0 2 (by decide))
      have e01 : delta x y h01 = delta x z h02 := by
        apply Subtype.ext
        exact hd01.trans hd02.symm
      have e12 : delta y z h12 = delta x z h02 := by
        apply Subtype.ext
        exact hd12.trans hd02.symm
      exact no_three_same_delta x y z h01 h12 h02 e01 e12
    · -- 情形 0 < k < ω：所有首差同为 k + 1
      let x := e (0 : Fin 5)
      let y := e (1 : Fin 5)
      let z := e (2 : Fin 5)
      have h01 : x ≠ y := e.injective.ne (by decide)
      have h12 : y ≠ z := e.injective.ne (by decide)
      have h02 : x ≠ z := e.injective.ne (by decide)
      have hd01 : (delta x y h01).val = k.val + 1 := by
        have hne0 : sharpColorValue h01 ≠ 0 := by
          intro hh
          exact hk0 ((valOf 0 1 (by decide)).symm.trans hh)
        have hneω : sharpColorValue h01 ≠ Ordinal.omega0.{u} := by
          intro hh
          exact hkω ((valOf 0 1 (by decide)).symm.trans hh)
        obtain ⟨hpos, hltω, hsub⟩ := sharpColorValue_middle h01 hne0 hneω
        exact sub_one_eq_iff hpos hltω (hsub.symm.trans (valOf 0 1 (by decide)))
      have hd12 : (delta y z h12).val = k.val + 1 := by
        have hne0 : sharpColorValue h12 ≠ 0 := by
          intro hh
          exact hk0 ((valOf 1 2 (by decide)).symm.trans hh)
        have hneω : sharpColorValue h12 ≠ Ordinal.omega0.{u} := by
          intro hh
          exact hkω ((valOf 1 2 (by decide)).symm.trans hh)
        obtain ⟨hpos, hltω, hsub⟩ := sharpColorValue_middle h12 hne0 hneω
        exact sub_one_eq_iff hpos hltω (hsub.symm.trans (valOf 1 2 (by decide)))
      have hd02 : (delta x z h02).val = k.val + 1 := by
        have hne0 : sharpColorValue h02 ≠ 0 := by
          intro hh
          exact hk0 ((valOf 0 2 (by decide)).symm.trans hh)
        have hneω : sharpColorValue h02 ≠ Ordinal.omega0.{u} := by
          intro hh
          exact hkω ((valOf 0 2 (by decide)).symm.trans hh)
        obtain ⟨hpos, hltω, hsub⟩ := sharpColorValue_middle h02 hne0 hneω
        exact sub_one_eq_iff hpos hltω (hsub.symm.trans (valOf 0 2 (by decide)))
      have e01 : delta x y h01 = delta x z h02 := by
        apply Subtype.ext
        exact hd01.trans hd02.symm
      have e12 : delta y z h12 = delta x z h02 := by
        apply Subtype.ext
        exact hd12.trans hd02.symm
      exact no_three_same_delta x y z h01 h12 h02 e01 e12

/- 2. 单色四元集。 -/

/-- 四元单色集的第 `(a,b)` 个分支：在 `ω` 以下由 `a` 控制坐标 `1`，
在坐标 `ω` 上取 `b`，其余坐标取 `false`。

这里用 `.val` 上的比较（`ξ.val = ω`、`ξ.val = 1`）而不是子类型上的相等，
这样「`γ < ω` 与 `ω` 不同」的证明只需一次 `ne_of_lt`。 -/
noncomputable def sharpBranch (a b : Bool) : Branch (Ordinal.omega0.{u} + 1) :=
  fun ξ => if ξ.val = Ordinal.omega0.{u} then b else if ξ.val = 1 then a else false

/-- `b` 不同则两分支不同（在坐标 `ω` 上取值不同）。 -/
theorem sharpBranch_ne_of_b {a b b' : Bool} (hb : b ≠ b') :
    (sharpBranch a b : Branch (Ordinal.omega0.{u} + 1)) ≠ sharpBranch a b' := by
  intro h
  have hv : b = b' := by
    simpa [sharpBranch, omegaCoord] using congrFun h omegaCoord
  exact hb hv

/-- `a` 不同则两分支不同（在坐标 `1` 上取值不同）。 -/
theorem sharpBranch_ne_of_a {a a' b b' : Bool} (ha : a ≠ a') :
    (sharpBranch a b : Branch (Ordinal.omega0.{u} + 1)) ≠ sharpBranch a' b' := by
  intro h
  have hv : a = a' := by
    simpa [sharpBranch, omegaCoord, coord1, one_ne_omega0'] using congrFun h coord1
  exact ha hv

/-- `(a,b) ↦ sharpBranch a b` 是单射：坐标 `ω` 恢复 `b`，坐标 `1` 恢复 `a`。 -/
theorem sharpBranch_injective : Function.Injective
    (fun p : Bool × Bool => (sharpBranch p.1 p.2 : Branch (Ordinal.omega0.{u} + 1))) := by
  intro p q hpq
  have hb : p.2 = q.2 := by
    simpa [sharpBranch, omegaCoord] using congrFun hpq omegaCoord
  have ha : p.1 = q.1 := by
    simpa [sharpBranch, omegaCoord, coord1, one_ne_omega0'] using congrFun hpq coord1
  exact Prod.ext ha hb

/-- 同一条限制、不同的 `b`：首差恰为 `ω`。 -/
theorem firstDiff_sharpBranch_omega {a b b' : Bool} (hb : b ≠ b') :
    FirstDifference (sharpBranch a b : Branch (Ordinal.omega0.{u} + 1))
      (sharpBranch a b') omegaCoord := by
  refine ⟨?_, ?_⟩
  · simpa [sharpBranch, omegaCoord] using hb
  · intro γ hγ
    have hγω : γ.val ≠ Ordinal.omega0.{u} := by
      exact ne_of_lt (by simpa [omegaCoord] using hγ)
    simp [sharpBranch, hγω]

/-- 不同的 `a`：首差恰为 `1`（坐标 `0` 上两者都是 `false`）。 -/
theorem firstDiff_sharpBranch_one {a a' b b' : Bool} (ha : a ≠ a') :
    FirstDifference (sharpBranch a b : Branch (Ordinal.omega0.{u} + 1))
      (sharpBranch a' b') coord1 := by
  refine ⟨?_, ?_⟩
  · simpa [sharpBranch, omegaCoord, coord1, one_ne_omega0'] using ha
  · intro γ hγ
    have hγ1 : γ.val < (1 : Ordinal.{u}) := by
      simpa only [coord1] using hγ
    have hγω : γ.val ≠ Ordinal.omega0.{u} := by
      intro hc
      rw [hc] at hγ1
      exact (not_lt_of_ge (le_of_lt Ordinal.one_lt_omega0)) hγ1
    have hγnot1 : γ.val ≠ (1 : Ordinal.{u}) := ne_of_lt hγ1
    simp [sharpBranch, hγω, hγnot1]

/-- `Fin 4` 到 `Bool × Bool` 的枚举：`0↦(F,F)`、`1↦(F,T)`、`2↦(T,F)`、`3↦(T,T)`。 -/
def fin4ToPair (i : Fin 4) : Bool × Bool :=
  (decide (2 ≤ i.val), decide (i.val % 2 = 1))

/-- 枚举是单射（`Fin 4` 只有 4 个点，直接判定）。 -/
theorem fin4ToPair_injective : Function.Injective fin4ToPair := by
  decide

/-- 四元单色集的嵌入。 -/
noncomputable def fourEmbedding : Fin 4 ↪ Branch (Ordinal.omega0.{u} + 1) where
  toFun i := sharpBranch (fin4ToPair i).1 (fin4ToPair i).2
  inj' := by
    intro i j h
    exact fin4ToPair_injective (sharpBranch_injective h)

/-- 单色集中任意两点的首差是 `1`（`a` 不同）或 `ω`（`a` 相同、`b` 不同）。 -/
theorem fourEmbedding_delta (i j : Fin 4) (hij : i ≠ j) :
    delta (fourEmbedding i) (fourEmbedding j) (fourEmbedding.injective.ne hij) =
        (coord1 : Set.Iio (Ordinal.omega0.{u} + 1)) ∨
    delta (fourEmbedding i) (fourEmbedding j) (fourEmbedding.injective.ne hij) =
        (omegaCoord : Set.Iio (Ordinal.omega0.{u} + 1)) := by
  classical
  let p := fin4ToPair i
  let q := fin4ToPair j
  have hpq : p ≠ q := by
    intro hp
    exact hij (fin4ToPair_injective (by simpa [p, q] using hp))
  have hxy : fourEmbedding i ≠ fourEmbedding j := fourEmbedding.injective.ne hij
  by_cases ha : p.1 = q.1
  · right
    have hb : p.2 ≠ q.2 := by
      intro hb'
      exact hpq (Prod.ext ha hb')
    have hFD0 : FirstDifference (sharpBranch p.1 p.2) (sharpBranch p.1 q.2) omegaCoord :=
      firstDiff_sharpBranch_omega hb
    have hFD : FirstDifference (fourEmbedding i) (fourEmbedding j) omegaCoord := by
      simpa [fourEmbedding, p, q, ha] using hFD0
    exact FirstDifference.unique (delta_spec (fourEmbedding i) (fourEmbedding j) hxy) hFD
  · left
    have hFD0 : FirstDifference (sharpBranch p.1 p.2) (sharpBranch q.1 q.2) coord1 :=
      firstDiff_sharpBranch_one ha
    have hFD : FirstDifference (fourEmbedding i) (fourEmbedding j) coord1 := by
      simpa [fourEmbedding, p, q] using hFD0
    exact FirstDifference.unique (delta_spec (fourEmbedding i) (fourEmbedding j) hxy) hFD

/-- Every edge of the explicit four-point witness has colour zero. -/
theorem fourEmbedding_colour_zero (i j : Fin 4) (hij : i ≠ j) :
    (sharpColoringC : PairColoring (Branch (Ordinal.omega0.{u} + 1))
      (Set.Iio (Ordinal.omega0.{u} + 1))).color (fourEmbedding i) (fourEmbedding j) =
        ⟨0, zero_lt_omega_add_one⟩ := by
  have hxy : fourEmbedding i ≠ fourEmbedding j := fourEmbedding.injective.ne hij
  have hval : sharpColorValue hxy = 0 := by
    rcases fourEmbedding_delta i j hij with hd | hd
    · exact sharpColorValue_of_delta_one hd
    · exact sharpColorValue_of_delta_omega hd
  apply Subtype.ext
  exact (sharpColoring_value hxy).trans hval

/-- The explicit zero-colour witness gives the four-clique in Theorem 2.3. -/
theorem sharpColoring_hasClique4 :
    (sharpColoringC : PairColoring (Branch (Ordinal.omega0.{u} + 1))
      (Set.Iio (Ordinal.omega0.{u} + 1))).HasClique 4 :=
  ⟨fourEmbedding, ⟨0, zero_lt_omega_add_one⟩, fourEmbedding_colour_zero⟩

/- 汇总。 -/

/-- **定理 2.3（完整证明）**：存在 ∆-regressive 染色，无单色五元集而有单色四元集。

这是 `Statements.lean` 中 `Theorem23` 的证明，全部由本仓库构造，
不依赖任何外部文献结果作为公理。 -/
theorem theorem_2_3 : Theorem23.{u} :=
  ⟨sharpColoringC, sharpColoring_regressive, sharpColoring_noClique5, sharpColoring_hasClique4⟩

end InfinitaryCombinatorics.Formalizations.A2

import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import InfinitaryCombinatorics.Delta
import InfinitaryCombinatorics.PairColoring
import Formalizations.A2.Basic

/-! The explicit sharp colouring at length omega + 1 and its regressivity. -/

namespace InfinitaryCombinatorics.Formalizations.A2

open Set
universe u

/- 坐标层面的基础设施：注意 `Set.Iio κ` 的成员性质字段是 `.property`。 -/

/-- `ω` 严格小于 `ω + 1`。 -/
theorem omega_lt_omega_add_one : Ordinal.omega0.{u} < Ordinal.omega0.{u} + 1 := by
  simp

/-- `0 < ω + 1`（用于构造颜色 `0`）。 -/
theorem zero_lt_omega_add_one : (0 : Ordinal.{u}) < Ordinal.omega0.{u} + 1 :=
  lt_of_le_of_lt bot_le omega_lt_omega_add_one

/-- `ω` 本身，视为 `ω+1` 的一个坐标。 -/
def omegaCoord : Set.Iio (Ordinal.omega0.{u} + 1) :=
  ⟨Ordinal.omega0.{u}, omega_lt_omega_add_one⟩

/-- 把 `ω` 以下的坐标提升为 `ω+1` 的坐标（因为 `ω < ω+1`）。 -/
def belowOmega (ξ : Set.Iio Ordinal.omega0.{u}) : Set.Iio (Ordinal.omega0.{u} + 1) :=
  ⟨ξ.val, lt_of_lt_of_le ξ.property (le_of_lt omega_lt_omega_add_one)⟩

/- 有限段上的减法：这是 ∆-regressive 验证的核心引理。 -/

/-- **自然数嵌入的序数加法可交换**：`1 + ↑n = ↑n + 1`。

重要：`Ordinal` **没有** `AddCommMagma` 实例——序数加法 genuinely 不交换
（`1 + ω = ω ≠ ω + 1`）。所以这里绝不能用 `add_comm`，只能借助
`Nat.cast_add` 把两侧都还原成自然数加法，再用 `Nat.add_comm`。
这个引理只覆盖**有限**的 `n`；无限序数要用别的手段。 -/
theorem one_add_natCast_eq_add_one (n : ℕ) :
    (1 : Ordinal.{u}) + (n : Ordinal.{u}) = (n : Ordinal.{u}) + 1 := by
  have hA : ((1 + n : ℕ) : Ordinal.{u}) = (1 : Ordinal.{u}) + (n : Ordinal.{u}) := by
    rw [Nat.cast_add]
    simp
  have hB : ((n + 1 : ℕ) : Ordinal.{u}) = (n : Ordinal.{u}) + 1 := by
    rw [Nat.cast_add]
    simp
  calc
    (1 : Ordinal.{u}) + (n : Ordinal.{u}) = ((1 + n : ℕ) : Ordinal.{u}) := hA.symm
    _ = ((n + 1 : ℕ) : Ordinal.{u}) := by rw [Nat.add_comm]
    _ = (n : Ordinal.{u}) + 1 := hB

/-- 有限正序数的前驱严格更小：`0 < d` 且 `d < ω` ⟹ `d - 1 < d`。

`sub_lt_of_le` 把它化归为 `d < 1 + d`；再用 `lt_omega0` 把 `d` 写成
自然数 `n`，问题就变成 `n < 1 + n`，由 `one_add_natCast_eq_add_one` 搬回 `n < n + 1`。
注意此引理**对 `d = ω` 不成立**（`1 + ω = ω`），因此不能用于无限序数。 -/
theorem sub_one_lt_of_lt_omega {d : Ordinal.{u}} (hd0 : 0 < d) (hdω : d < Ordinal.omega0.{u}) :
    d - 1 < d := by
  have h1le : (1 : Ordinal.{u}) ≤ d := by
    simpa [Order.succ_eq_add_one] using (Order.succ_le_iff).2 hd0
  apply (Ordinal.sub_lt_of_le h1le).2
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdω
  calc
    (n : Ordinal.{u}) < (n : Ordinal.{u}) + 1 := by
      simp
    _ = 1 + (n : Ordinal.{u}) := by
      exact (one_add_natCast_eq_add_one n).symm

/- 手稿式 (1) 的染色。 -/

/-- 颜色值（序数形式），仅在 `x ≠ y` 时调用。 -/
noncomputable def sharpColorValue {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y) :
    Ordinal.{u} :=
  let d := (delta x y hxy).val
  if d = 0 then Ordinal.omega0.{u}
  else if d < Ordinal.omega0.{u} then d - 1
  else 0

/-- 颜色值确实落在 `ω+1` 内。 -/
theorem sharpColorValue_lt {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y) :
    sharpColorValue hxy < Ordinal.omega0.{u} + 1 := by
  unfold sharpColorValue
  dsimp
  by_cases h0 : (delta x y hxy).val = 0
  · rw [if_pos h0]
    exact omega_lt_omega_add_one
  · rw [if_neg h0]
    by_cases hlt : (delta x y hxy).val < Ordinal.omega0.{u}
    · rw [if_pos hlt]
      exact lt_of_le_of_lt (Ordinal.sub_le_self _ _) (lt_trans hlt omega_lt_omega_add_one)
    · rw [if_neg hlt]
      exact zero_lt_omega_add_one

/-- 颜色值对调两点后不变：`delta` 的取值与不等证明的具体项无关
（两个 `x ≠ y` 的证明在 Lean 核中定义相等，故 `delta_symm` 可直接用）。

注意：不要把这个引理放进 `simp` 的集合里（`simp [sharpColorValue_symm]`
会与自身反向匹配而循环）；下面一律用 `rw`/`simpa ... using`。 -/
theorem sharpColorValue_symm {x y : Branch (Ordinal.omega0.{u} + 1)} (hxy : x ≠ y) :
    sharpColorValue hxy = sharpColorValue (fun h => hxy h.symm) := by
  unfold sharpColorValue
  dsimp
  have hd : delta x y hxy = delta y x (fun h => hxy h.symm) := by
    simpa only using delta_symm x y hxy
  rw [hd]

/-- 定理 2.3 的显式染色 `c : [2^(ω+1)]² → ω+1`。 -/
noncomputable def sharpColoring :
    PairColoring (Branch (Ordinal.omega0.{u} + 1)) (Set.Iio (Ordinal.omega0.{u} + 1)) where
  color x y := by
    classical
    exact if hxy : x = y then ⟨0, zero_lt_omega_add_one⟩
      else ⟨sharpColorValue hxy, sharpColorValue_lt hxy⟩
  symm x y := by
    classical
    by_cases hxy : x = y
    · subst hxy
      rfl
    · have hyx : y ≠ x := fun h => hxy h.symm
      apply Subtype.ext
      simpa [hxy, hyx] using (sharpColorValue_symm hxy)

/-- **定理 2.3 的 ∆-regressive 验证**（完整证明）。

对手稿式 (1) 的三个分支分别验证 `0 < ∆ ⟹ c(x,y) < ∆`：

- `∆ = 0`：前提 `0 < 0` 不成立，命题空洞成立；
- `0 < ∆ < ω`：颜色是 `∆ - 1`，由 `sub_one_lt_of_lt_omega` 严格小于 `∆`；
- `∆ ≥ ω`：`∆` 只能是 `ω`（因为坐标集是 `ω+1`），颜色为 `0`，
  而 `0 < ω ≤ ∆`，故 `0 < ∆`。 -/
theorem sharpColoring_regressive :
    DeltaRegressive (Ordinal.omega0.{u} + 1) (sharpColoring : PairColoring (Branch (Ordinal.omega0.{u} + 1)) (Set.Iio (Ordinal.omega0.{u} + 1))) := by
  intro x y hxy hpos
  simp [sharpColoring, hxy]
  unfold sharpColorValue
  dsimp
  by_cases h0 : (delta x y hxy).val = 0
  · rw [if_pos h0]
    rw [h0] at hpos
    exact False.elim (not_lt_zero hpos)
  · rw [if_neg h0]
    have hd0 : 0 < (delta x y hxy).val := by
      exact lt_of_le_of_ne bot_le (by
        intro hz
        exact h0 hz.symm)
    by_cases hlt : (delta x y hxy).val < Ordinal.omega0.{u}
    · rw [if_pos hlt]
      exact sub_one_lt_of_lt_omega hd0 hlt
    · rw [if_neg hlt]
      exact hd0

end InfinitaryCombinatorics.Formalizations.A2

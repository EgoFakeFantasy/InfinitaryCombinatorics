import Mathlib.SetTheory.Ordinal.Basic
import InfinitaryCombinatorics.Delta
import InfinitaryCombinatorics.PairColoring

/-! Cones and the fixed-colour four-point lemma (Lemma 3.1). -/

namespace InfinitaryCombinatorics.Formalizations.A2

open Set
universe u

variable {κ : Ordinal.{u}}

/-- 论文的锥 `N_s`：在坐标集 `coords` 上与模式 `s` 一致的分支集合。

用坐标集合而非自然数前段来表达，可以同时覆盖有限前段与单点条件，
且不必处理 `ℕ` 到 `Ordinal` 的强制转换。有限前段取
`coords = {ξ | ξ.val < n}` 即可。 -/
def Cone (κ : Ordinal.{u}) (coords : Set (Set.Iio κ)) (s : Set.Iio κ → Bool) :
    Set (Branch κ) :=
  {x | ∀ ξ ∈ coords, x ξ = s ξ}

/-- 首位为 `false`（即论文的第 0 位为 0）的锥 `N⟨0⟩`。 -/
def zeroCone (κ : Ordinal.{u}) (h0 : (0 : Ordinal.{u}) < κ) : Set (Branch κ) :=
  {x | x ⟨0, h0⟩ = false}

/-- 空坐标约束给出全空间。 -/
theorem cone_empty (s : Set.Iio κ → Bool) : Cone κ ∅ s = Set.univ := by
  ext x
  simp [Cone]

/-- 坐标约束越多，锥越小。 -/
theorem cone_mono {coords₁ coords₂ : Set (Set.Iio κ)} (h : coords₁ ⊆ coords₂)
    (s : Set.Iio κ → Bool) : Cone κ coords₂ s ⊆ Cone κ coords₁ s := by
  intro x hx ξ hξ
  exact hx ξ (h hξ)

/-- 锥对模式是单调的：逐坐标相等则锥相同。 -/
theorem cone_congr (coords : Set (Set.Iio κ)) {s t : Set.Iio κ → Bool}
    (hst : ∀ ξ ∈ coords, s ξ = t ξ) : Cone κ coords s = Cone κ coords t := by
  ext x
  constructor
  · intro hx ξ hξ
    exact (hx ξ hξ).trans (hst ξ hξ)
  · intro hx ξ hξ
    exact (hx ξ hξ).trans (hst ξ hξ).symm

/-
  引理 3.1（纯有限，完整证明）
  注意：Lean 的块注释是 `/- -/`，不支持 C 风格的 `/* */`。
-/

/-- 论文引理 3.1，显式四元组表述。

若 `A`、`B` 不交，所有 `A`–`B` 交叉边都是颜色 `m`，且两侧各含一条 `m` 色内边，
则 `A ∪ B` 中有一个 `m` 色的单色四元集：两条内边加四条交叉边，共六条。 -/
theorem lemma_3_1 {V : Type*} {K : Type*} (c : PairColoring V K) (m : K)
    {A B : Set V} (hdisj : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, c.color a b = m)
    (hA : ∃ a₀ ∈ A, ∃ a₁ ∈ A, a₀ ≠ a₁ ∧ c.color a₀ a₁ = m)
    (hB : ∃ b₀ ∈ B, ∃ b₁ ∈ B, b₀ ≠ b₁ ∧ c.color b₀ b₁ = m) :
    ∃ a₀ ∈ A, ∃ a₁ ∈ A, ∃ b₀ ∈ B, ∃ b₁ ∈ B,
      a₀ ≠ a₁ ∧ b₀ ≠ b₁ ∧
      a₀ ≠ b₀ ∧ a₀ ≠ b₁ ∧ a₁ ≠ b₀ ∧ a₁ ≠ b₁ ∧
      c.color a₀ a₁ = m ∧ c.color b₀ b₁ = m ∧
      c.color a₀ b₀ = m ∧ c.color a₀ b₁ = m ∧
      c.color a₁ b₀ = m ∧ c.color a₁ b₁ = m := by
  rcases hA with ⟨a₀, ha₀, a₁, ha₁, ha01, hca⟩
  rcases hB with ⟨b₀, hb₀, b₁, hb₁, hb01, hcb⟩
  have hdisj' : ∀ {x}, x ∈ A → x ∈ B → False :=
    fun hx hy => Set.disjoint_left.mp hdisj hx hy
  have ha₀b₀ : a₀ ≠ b₀ := by
    intro h
    exact hdisj' ha₀ (h ▸ hb₀)
  have ha₀b₁ : a₀ ≠ b₁ := by
    intro h
    exact hdisj' ha₀ (h ▸ hb₁)
  have ha₁b₀ : a₁ ≠ b₀ := by
    intro h
    exact hdisj' ha₁ (h ▸ hb₀)
  have ha₁b₁ : a₁ ≠ b₁ := by
    intro h
    exact hdisj' ha₁ (h ▸ hb₁)
  refine ⟨a₀, ha₀, a₁, ha₁, b₀, hb₀, b₁, hb₁,
    ha01, hb01, ha₀b₀, ha₀b₁, ha₁b₀, ha₁b₁, hca, hcb, ?_, ?_, ?_, ?_⟩
  · exact hcross a₀ ha₀ b₀ hb₀
  · exact hcross a₀ ha₀ b₁ hb₁
  · exact hcross a₁ ha₁ b₀ hb₀
  · exact hcross a₁ ha₁ b₁ hb₁

end InfinitaryCombinatorics.Formalizations.A2

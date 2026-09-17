import InfinitaryCombinatorics.PairColoring
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Order.WellFounded

/-! First differences on arbitrary well-ordered coordinate types, including uncountable ones. -/
namespace InfinitaryCombinatorics
open Set
universe u v
variable {ι : Type u} {B : Type v} [LinearOrder ι]

def FirstDifference (x y : ι → B) (δ : ι) : Prop :=
  x δ ≠ y δ ∧ ∀ γ < δ, x γ = y γ

theorem FirstDifference.symm {x y : ι → B} {δ : ι} (h : FirstDifference x y δ) :
    FirstDifference y x δ := ⟨h.1.symm, fun γ hγ => (h.2 γ hγ).symm⟩

theorem FirstDifference.unique {x y : ι → B} {δ ε : ι}
    (hδ : FirstDifference x y δ) (hε : FirstDifference x y ε) : δ = ε := by
  rcases lt_trichotomy δ ε with h | h | h
  · exact (hδ.1 (hε.2 δ h)).elim
  · exact h
  · exact (hε.1 (hδ.2 ε h)).elim

theorem FirstDifference.ne {x y : ι → B} {δ : ι} (h : FirstDifference x y δ) : x ≠ y :=
  fun hxy => h.1 (congrFun hxy δ)

/-- If the second pair agrees beyond the first split, the first split is unchanged. -/
theorem FirstDifference.of_lt {x y z : ι → B} {δ ε : ι}
    (hxy : FirstDifference x y δ) (hyz : FirstDifference y z ε) (hδε : δ < ε) :
    FirstDifference x z δ := by
  refine ⟨?_, fun γ hγ => (hxy.2 γ hγ).trans (hyz.2 γ (hγ.trans hδε))⟩
  intro hxz
  exact hxy.1 (hxz.trans (hyz.2 δ hδε).symm)

/-- Three binary branches cannot have their first difference at the same coordinate. -/
theorem binary_no_three_same_split {x y z : ι → Bool} {δ : ι}
    (hxy : FirstDifference x y δ) (hyz : FirstDifference y z δ) :
    ¬ FirstDifference x z δ := by
  intro hxz
  have h₁ := hxy.1
  have h₂ := hyz.1
  have h₃ := hxz.1
  cases hx : x δ <;> cases hy : y δ <;> cases hz : z δ <;> simp_all

section WellOrdered
variable [WellFoundedLT ι]

omit [LinearOrder ι] [WellFoundedLT ι] in
private theorem difference_nonempty (x y : ι → B) (hxy : x ≠ y) :
    {δ | x δ ≠ y δ}.Nonempty := by
  by_contra h
  apply hxy
  funext δ
  by_contra hd
  exact h ⟨δ, hd⟩

noncomputable def delta (x y : ι → B) (hxy : x ≠ y) : ι :=
  wellFounded_lt.min {δ | x δ ≠ y δ} (difference_nonempty x y hxy)

theorem delta_spec (x y : ι → B) (hxy : x ≠ y) : FirstDifference x y (delta x y hxy) := by
  refine ⟨wellFounded_lt.min_mem {δ | x δ ≠ y δ} (difference_nonempty x y hxy), ?_⟩
  intro γ hγ
  by_contra hn
  exact wellFounded_lt.not_lt_min {δ | x δ ≠ y δ} hn hγ

theorem delta_symm (x y : ι → B) (hxy : x ≠ y) :
    delta x y hxy = delta y x hxy.symm :=
  (delta_spec x y hxy).symm.unique (delta_spec y x hxy.symm)

theorem delta_triangle (x y z : ι → B) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    min (delta x y hxy) (delta y z hyz) ≤ delta x z hxz := by
  by_contra hn
  have h := lt_of_not_ge hn
  have h₁ := (delta_spec x y hxy).2 _ (lt_of_lt_of_le h (min_le_left _ _))
  have h₂ := (delta_spec y z hyz).2 _ (lt_of_lt_of_le h (min_le_right _ _))
  exact (delta_spec x z hxz).1 (h₁.trans h₂)

end WellOrdered

abbrev Branch (κ : Ordinal.{u}) := Set.Iio κ → Bool

/-- Only positive first differences impose a bound, exactly as in the register. -/
def DeltaRegressive (κ : Ordinal.{u}) (c : PairColoring (Branch κ) (Set.Iio κ)) : Prop :=
  ∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
    (c.color x y).val < (delta x y hxy).val

end InfinitaryCombinatorics


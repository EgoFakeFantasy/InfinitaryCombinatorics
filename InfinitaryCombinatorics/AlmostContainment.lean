import R0.Basic

/-! Finite-error containment on arbitrary sets. -/
namespace InfinitaryCombinatorics
open Set
universe u
variable {X : Type u} {a b c : Set X}

def AlmostSubset (a b : Set X) : Prop := (a \ b).Finite

theorem AlmostSubset.refl (a : Set X) : AlmostSubset a a := by
  simp [AlmostSubset]

theorem almostSubset_of_subset (h : a ⊆ b) : AlmostSubset a b := by
  simp [AlmostSubset, diff_eq_empty.mpr h]

theorem AlmostSubset.trans (hab : AlmostSubset a b) (hbc : AlmostSubset b c) :
    AlmostSubset a c := by
  apply (hab.union hbc).subset
  intro x hx
  by_cases hxb : x ∈ b
  · exact Or.inr ⟨hxb, hx.2⟩
  · exact Or.inl ⟨hx.1, hxb⟩

theorem AlmostSubset.inter (hab : AlmostSubset a b) (hac : AlmostSubset a c) :
    AlmostSubset a (b ∩ c) := by
  unfold AlmostSubset at *
  simpa [diff_inter] using hab.union hac

theorem AlmostSubset.infinite (hab : AlmostSubset a b) (ha : a.Infinite) : b.Infinite := by
  apply (ha.diff hab).mono
  intro x hx
  by_contra hxb
  exact hx.2 ⟨hx.1, hxb⟩

theorem almostSubset_iff_eventually {a b : Set ℕ} :
    AlmostSubset a b ↔ ∃ N, ∀ n ≥ N, n ∈ a → n ∈ b := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h.bddAbove
    refine ⟨N + 1, ?_⟩
    intro n hn ha
    by_contra hb
    have := hN (show n ∈ a \ b from ⟨ha, hb⟩)
    omega
  · rintro ⟨N, hN⟩
    apply (finite_lt_nat N).subset
    intro n hn
    by_contra h
    exact hn.2 (hN n (Nat.le_of_not_gt h) hn.1)

end InfinitaryCombinatorics


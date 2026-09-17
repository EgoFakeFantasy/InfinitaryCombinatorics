import InfinitaryCombinatorics.Ideal

namespace InfinitaryCombinatorics
open Set
universe u
variable {X : Type u}

abbrev FinSequence := R0.FinSequence
abbrev FinIntersecting := @R0.FinIntersecting
abbrev Splits := R0.Splits
abbrev Splitting := R0.Splitting
noncomputable abbrev splittingNumber := R0.splittingNumber

theorem centered_mono {S T : Set (Set ℕ)} (hT : R0.Centered T) (hST : S ⊆ T) :
    R0.Centered S := fun F hF => hT F (hF.trans hST)

theorem finIntersecting_mono {A B : Set (Set X)} (hB : R0.FinIntersecting B)
    (hAB : A ⊆ B) : R0.FinIntersecting A := by
  intro C
  obtain ⟨i, hi, hBi⟩ := hB C
  refine ⟨i, hi, centered_mono hBi ?_⟩
  rintro t ⟨ht, a, ha, rfl⟩
  exact ⟨ht, a, hAB ha, rfl⟩

theorem not_finIntersecting_of_subset {A B : Set (Set X)}
    (hA : ¬ R0.FinIntersecting A) (hAB : A ⊆ B) : ¬ R0.FinIntersecting B :=
  fun hB => hA (finIntersecting_mono hB hAB)

/-- A two-trace obstruction suffices; no AD assumption is needed. -/
theorem not_finIntersecting_of_split_traces (A : Set (Set X)) (C : FinSequence X)
    (h : ∀ i : Set ℕ, i.Infinite → ∃ a ∈ A, ∃ b ∈ A,
      (i ∩ R0.trace C a).Infinite ∧ (i ∩ R0.trace C b).Infinite ∧
      Disjoint (i ∩ R0.trace C a) (i ∩ R0.trace C b)) : ¬ R0.FinIntersecting A := by
  intro hA
  obtain ⟨i, hi, hcenter⟩ := hA C
  obtain ⟨a, ha, b, hb, hia, hib, hd⟩ := h i hi
  exact R0.not_centered_of_disjoint (T := R0.retainedTraces C A i)
    ⟨hia, a, ha, rfl⟩ ⟨hib, b, hb, rfl⟩ hd.eq_bot hcenter

end InfinitaryCombinatorics


import Formalizations

open Set Cardinal R0

/-- Existence on the actual natural numbers, with the predicates unfolded.
In particular, all infinite retained traces participate in every nonempty
finite intersection test; no predetermined witness family is assumed. -/
example : ∃ A : Set (Set ℕ),
    (A.Infinite ∧ (∀ a ∈ A, a.Infinite) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite) ∧
    ¬ (∀ C : FinSequence ℕ, ∃ i : Set ℕ, i.Infinite ∧
      ∀ F : Set (Set ℕ),
        (∀ t ∈ F, t.Infinite ∧ ∃ a ∈ A, t = i ∩ {n | (a ∩ C.block n).Nonempty}) →
        F.Finite → F.Nonempty → (⋂ t ∈ F, t).Infinite) ∧
    #A = splittingNumber := by
  simpa only [AlmostDisjoint, FinIntersecting, Centered, retainedTraces,
    trace, Set.subset_def, Set.mem_setOf_eq] using
    InfinitaryCombinatorics.Formalizations.R0.exists_counterexample_of_size_s

example (A : Set (Set ℕ)) (hA : #A < splittingNumber) : FinIntersecting A :=
  InfinitaryCombinatorics.Formalizations.R0.small_families_are_finIntersecting A hA

example : IsLeast {κ : Cardinal | ∃ A : Set (Set ℕ),
    AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = κ} splittingNumber :=
  InfinitaryCombinatorics.Formalizations.R0.least_counterexample_cardinal

example : nonFinIntersectingNumber = splittingNumber :=
  InfinitaryCombinatorics.Formalizations.R0.nonFinIntersectingNumber_eq_splittingNumber

#print axioms InfinitaryCombinatorics.Formalizations.R0.exists_counterexample_of_size_s
#print axioms InfinitaryCombinatorics.Formalizations.R0.nonFinIntersectingNumber_eq_splittingNumber

namespace A1Acceptance
open InfinitaryCombinatorics InfinitaryCombinatorics.Formalizations.A1

example (C : LadderSystem) (h : TypeGuessingOnPoints C widthSeq typeSeqW) :
    ∀ D : Set Point, IsClub D → ∃ β : LimitBelow omegaOne, ∀ m ≥ 1,
      ∃ x ∈ D, (C β).seq (3 * m) ≤ x.val ∧ x.val < (C β).seq (3 * m + 3) := by
  intro D hD
  simpa only [Hits, thin_seq, Nat.mul_add, Nat.mul_one] using
    typeGuessing_implies_hits_thin C ((typeGuessing_iff_allPoints C widthSeq typeSeqW).mpr h) D hD

#print axioms typeGuessing_implies_K_thin
#print axioms antiColoring_on_omegaOne
#print axioms BDTG_implies_KA
#print axioms Diamond_implies_ClubGuessing
#print axioms KA_implies_KAomegaOne
end A1Acceptance

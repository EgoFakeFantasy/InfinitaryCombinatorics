import InfinitaryCombinatorics.FinIntersection

namespace InfinitaryCombinatorics
open Set
universe u
variable {X : Type u}

/-- Families of nonempty finite sets that meet the complement of every ideal member. -/
def PositiveFinFamily (A : Set (Set X)) (F : Set (Set X)) : Prop :=
  (∀ s ∈ F, s.Finite ∧ s.Nonempty) ∧
  ∀ b, InIdeal A b → ∃ s ∈ F, Disjoint s b

def SS (A : Set (Set X)) : Prop :=
  ∀ F, PositiveFinFamily A F → ∃ b, InIdeal A b ∧ {s ∈ F | s ⊆ b}.Infinite

def AlmostStronglySeparable (A : Set (Set X)) : Prop :=
  ∀ F, PositiveFinFamily A F → ∃ a ∈ A, {s ∈ F | s ⊆ a}.Infinite

theorem almostStronglySeparable_implies_SS {A : Set (Set X)}
    (h : AlmostStronglySeparable A) : SS A := by
  intro F hF
  obtain ⟨a, ha, hFa⟩ := h F hF
  exact ⟨a, inIdeal_of_mem ha, hFa⟩

/-- A8's extension obstacle remains an explicit hypothesis in this reuse theorem. -/
theorem nonFI_mad_extension {A B : Set (Set X)} (hA : ¬ R0.FinIntersecting A)
    (hAB : A ⊆ B) (hB : MAD B) : MAD B ∧ ¬ R0.FinIntersecting B :=
  ⟨hB, not_finIntersecting_of_subset hA hAB⟩

end InfinitaryCombinatorics

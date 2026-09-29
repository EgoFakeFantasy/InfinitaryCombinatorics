import Formalizations.FIMAD.SeparationCardinal

/-! The Dow cardinal is defined from actual orthogonal families, rather than
being a free cardinal parameter. The comparison dp ≤ ap is proved directly
from inseparable cuts in an almost disjoint family. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal

def OrthogonalFamilies (A B : Set (Set ℕ)) : Prop :=
  (∀ a ∈ A, a.Infinite) ∧ (∀ b ∈ B, b.Infinite) ∧
    ∀ a ∈ A, ∀ b ∈ B, (a ∩ b).Finite

def WeaklySeparates (X : Set ℕ) (A B : Set (Set ℕ)) : Prop :=
  (∀ a ∈ A, (a ∩ X).Infinite) ∧ ∀ b ∈ B, (b ∩ X).Finite

def dowCardinals : Set Cardinal :=
  {κ | ∃ A B : Set (Set ℕ), OrthogonalFamilies A B ∧
    (¬ ∃ X, WeaklySeparates X A B) ∧ #(A ∪ B : Set (Set ℕ)) = κ}

noncomputable def dowNumber : Cardinal := sInf dowCardinals

theorem nonseparableCardinals_subset_dowCardinals :
    nonseparableCardinals ⊆ dowCardinals := by
  classical
  rintro κ ⟨A, hA, hn, hcard⟩
  have hcut : ∃ B ⊆ A, ¬ ∃ X : Set ℕ, ∀ a ∈ A, (a ∩ X).Infinite ↔ a ∈ B := by
    by_contra hh
    apply hn
    intro B hBA
    by_contra hb
    exact hh ⟨B, hBA, hb⟩
  obtain ⟨B, hBA, hB⟩ := hcut
  refine ⟨B, A \ B, ?_, ?_, ?_⟩
  · refine ⟨fun a ha => hA.1 a (hBA ha), fun b hb => hA.1 b hb.1, ?_⟩
    intro a ha b hb
    exact hA.2 a (hBA ha) b hb.1 (fun hab => hb.2 (hab ▸ ha))
  · rintro ⟨X, hX⟩
    apply hB
    refine ⟨X, fun a ha => ⟨?_, ?_⟩⟩
    · intro hi
      by_contra hnot
      exact hi (hX.2 a ⟨ha, hnot⟩)
    · exact fun hb => hX.1 a hb
  · have heq : B ∪ (A \ B) = A := union_diff_cancel hBA
    rw [heq]
    exact hcard

theorem dowCardinals_nonempty : dowCardinals.Nonempty :=
  nonseparableCardinals_nonempty.mono nonseparableCardinals_subset_dowCardinals

theorem exists_minimum_dow :
    ∃ A B : Set (Set ℕ), OrthogonalFamilies A B ∧
      (¬ ∃ X, WeaklySeparates X A B) ∧ #(A ∪ B : Set (Set ℕ)) = dowNumber :=
  csInf_mem dowCardinals_nonempty

theorem dowNumber_le_almostDisjointSeparationNumber :
    dowNumber ≤ almostDisjointSeparationNumber := by
  obtain ⟨A, hA, hn, hc⟩ := exists_minimum_nonseparable
  exact csInf_le' (nonseparableCardinals_subset_dowCardinals ⟨A, hA, hn, hc⟩)

theorem weaklySeparates_of_card_lt_dow {A B : Set (Set ℕ)}
    (hAB : OrthogonalFamilies A B) (hc : #(A ∪ B : Set (Set ℕ)) < dowNumber) :
    ∃ X, WeaklySeparates X A B := by
  by_contra hn
  exact (not_le_of_gt hc) (csInf_le' ⟨A, B, hAB, hn, rfl⟩)

/-- A negative conclusion usable directly from a model's s < dp inequality. -/
theorem no_fi_mad_of_s_lt_dp (h : R0.splittingNumber < dowNumber) :
    ¬ ∃ A : Set (Set ℕ), MAD A ∧ R0.FinIntersecting A :=
  no_fi_mad_of_s_lt_ap (h.trans_le dowNumber_le_almostDisjointSeparationNumber)

end InfinitaryCombinatorics.Formalizations.FIMAD

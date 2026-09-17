import Formalizations.A1.Main

/-! # The family version of Kunen's principle (manuscript Lemma 7.4) -/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order Cardinal
noncomputable section

/-- A set of order type omega is supplied with its increasing enumeration. -/
abbrev OmegaEnumeration := ℕ ↪o Point

/-- The family version at cardinal omega one. The family consists of sets, not repeated indices. -/
def KAomegaOne : Prop :=
  ∃ X : Set (Set Point), #X ≤ ℵ₁ ∧
    (∀ s ∈ X, ∃ a : OmegaEnumeration, Set.range a = s) ∧
    ∀ D : Set Point, IsClub D → ∃ s ∈ X, ∃ a : OmegaEnumeration,
      Set.range a = s ∧ ∃ N : ℕ, ∀ m ≥ N, ∃ x ∈ D, a m ≤ x ∧ x < a (m + 1)

/-- A ladder's increasing enumeration in the full ordinal domain. -/
def ladderEnumeration (C : LadderSystem) (β : LimitBelow omegaOne) : OmegaEnumeration :=
  OrderEmbedding.ofStrictMono (ladderPoint C β) (ladderPoint_strictMono C β)

theorem limitBelow_card_le : #(LimitBelow omegaOne) ≤ ℵ₁ := by
  have h : #(LimitBelow omegaOne) ≤ #Point :=
    Cardinal.mk_le_of_injective (f := limitPoint) (by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Point => z.val) hxy)
  calc
    #(LimitBelow omegaOne) ≤ #Point := h
    _ = ℵ₁ := by
      rw [Cardinal.mk_Iio_ordinal, Ordinal.card_omega, Cardinal.lift_aleph]
      simp

/-- The ladder system's image family witnesses the family version. -/
theorem KA_implies_KAomegaOne : KA → KAomegaOne := by
  rintro ⟨C, hC⟩
  let X : Set (Set Point) := Set.range fun β => Set.range (ladderEnumeration C β)
  refine ⟨X, Cardinal.mk_range_le.trans limitBelow_card_le, ?_, ?_⟩
  · rintro s ⟨β, rfl⟩
    exact ⟨ladderEnumeration C β, rfl⟩
  · intro D hD
    obtain ⟨β, N, hβ⟩ := hC D hD
    refine ⟨Set.range (ladderEnumeration C β), ⟨β, rfl⟩,
      ladderEnumeration C β, rfl, N, ?_⟩
    intro m hm
    exact hβ m hm

theorem not_KA_of_not_KAomegaOne (h : ¬ KAomegaOne) : ¬ KA :=
  fun hKA => h (KA_implies_KAomegaOne hKA)

end
end InfinitaryCombinatorics.Formalizations.A1

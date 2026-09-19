import Formalizations.R0.CountableTransfer

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

lemma countable_incidence_of_extension {E K : Set (Set X)} (hK : ADFamily K) (hEK : E ⊆ K) :
    CountableIncidence E K := by
  intro n hn
  apply (countable_singleton n).mono
  intro a ha
  apply mem_singleton_iff.mpr
  by_contra han
  exact ha.2 (hK.2 a (hEK ha.1) n hn han)

lemma cardinal_le_of_countable_incidence {E N : Set (Set X)} (hE : ADFamily E)
    (hN : MAD N) (hinc : CountableIncidence E N) : #E ≤ #N := by
  have hcover : E ⊆ refinement N (incidence E) := by
    intro a ha
    obtain ⟨n, hn, hi⟩ := hN.2 a (hE.1 a ha)
    exact mem_refinement.mpr ⟨n, hn, ha, hi⟩
  have hω : ℵ₀ ≤ #N := Cardinal.aleph0_le_mk_iff.mpr hN.1.1.to_subtype
  calc
    #E ≤ #(refinement N (incidence E)) := Cardinal.mk_le_mk_of_subset hcover
    _ ≤ #N * ⨆ n : N, #(incidence E n.val) := Cardinal.mk_biUnion_le _ _
    _ ≤ #N * ℵ₀ := mul_le_mul_right (ciSup_le' (fun n : N =>
      Cardinal.le_aleph0_iff_set_countable.mpr (hinc n n.property))) _
    _ = #N := Cardinal.mul_aleph0_eq hω

def placementCardinals (E : Set (Set X)) : Set Cardinal :=
  {κ | ∃ N : Set (Set X), MAD N ∧ CountableIncidence E N ∧ #N = κ}

noncomputable def placementNumber (E : Set (Set X)) : Cardinal := sInf (placementCardinals E)

lemma placementCardinals_nonempty {E : Set (Set X)} (hE : _root_.R0.AlmostDisjoint E) :
    (placementCardinals E).Nonempty := by
  obtain ⟨K, hEK, hK, _⟩ := minimum_cost_completion hE
  exact ⟨#K, K, hK, countable_incidence_of_extension hK.1.2 hEK, rfl⟩

lemma exists_minimum_placement {E : Set (Set X)} (hE : _root_.R0.AlmostDisjoint E) :
    ∃ N : Set (Set X), MAD N ∧ CountableIncidence E N ∧ #N = placementNumber E :=
  csInf_mem (placementCardinals_nonempty hE)

lemma placementNumber_le {E N : Set (Set X)} (hN : MAD N) (hinc : CountableIncidence E N) :
    placementNumber E ≤ #N := csInf_le' ⟨N, hN, hinc, rfl⟩

/-- Paper Proposition 6.4, for genuinely infinite AD seeds. -/
theorem placement_formula [Countable X] [Infinite X] {E : Set (Set X)}
    (hE : _root_.R0.AlmostDisjoint E) :
    placementNumber E = max #E (extensionCost E univ) := by
  apply le_antisymm
  · obtain ⟨K, hEK, hK, hcard⟩ := minimum_cost_completion hE
    exact (placementNumber_le hK (countable_incidence_of_extension hK.1.2 hEK)).trans_eq hcard
  · obtain ⟨N, hN, hinc, hcard⟩ := exists_minimum_placement hE
    have he : extensionCost E univ ≤ #N := by
      simpa only [max_eq_left (mad_card_lower hN)] using
        extensionCost_le_of_countable_incidence hE.2 hN hinc
    exact (max_le (cardinal_le_of_countable_incidence hE.2 hN hinc) he).trans_eq hcard

/-- Countable-incidence placement of size a is exactly the bounded-cost condition. -/
theorem placement_at_a_iff [Countable X] [Infinite X] {E : Set (Set X)}
    (hE : _root_.R0.AlmostDisjoint E) (hEc : #E ≤ almostDisjointnessNumber) :
    (∃ N : Set (Set X), MAD N ∧ #N = almostDisjointnessNumber ∧ CountableIncidence E N) ↔
      extensionCost E univ ≤ almostDisjointnessNumber := by
  constructor
  · rintro ⟨N, hN, hcard, hinc⟩
    simpa only [hcard, max_self] using extensionCost_le_of_countable_incidence hE.2 hN hinc
  · intro he
    obtain ⟨K, hEK, hK, hcard⟩ := minimum_cost_completion hE
    exact ⟨K, hK, le_antisymm (hcard.le.trans (max_le hEc he)) (mad_card_lower hK),
      countable_incidence_of_extension hK.1.2 hEK⟩

end InfinitaryCombinatorics.Formalizations.R0

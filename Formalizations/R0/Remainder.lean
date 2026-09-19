import Formalizations.R0.Local

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

/-- Relative maximality is proved for an arbitrary pool of infinite sets. -/
lemma exists_relative_maximal (Q : Set (Set X)) (hQ : ∀ Y ∈ Q, Y.Infinite) :
    ∃ H, ADFamily H ∧ H ⊆ Q ∧ ∀ Y ∈ Q, ∃ h ∈ H, (Y ∩ h).Infinite := by
  classical
  let B : Set (Set (Set X)) := {H | ADFamily H ∧ H ⊆ Q}
  have hub : ∀ c ⊆ B, IsChain (· ⊆ ·) c → ∃ H ∈ B, ∀ D ∈ c, D ⊆ H := by
    intro c hc hchain
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun D hD => subset_sUnion_of_mem hD⟩
    · constructor
      · rintro Y ⟨D, hD, hY⟩; exact (hc hD).1.1 Y hY
      · rintro Y ⟨D, hD, hY⟩ Z ⟨E, hE, hZ⟩ hYZ
        by_cases hDE : D = E
        · subst E; exact (hc hD).1.2 Y hY Z hZ hYZ
        · rcases hchain hD hE hDE with h | h
          · exact (hc hE).1.2 Y (h hY) Z hZ hYZ
          · exact (hc hD).1.2 Y hY Z (h hZ) hYZ
    · rintro Y ⟨D, hD, hY⟩; exact (hc hD).2 hY
  obtain ⟨H, hm⟩ := zorn_subset B hub
  refine ⟨H, hm.1.1, hm.1.2, ?_⟩
  intro Y hY
  by_contra hn
  have ho : Y ∈ Orthogonal H := fun h hh =>
    not_infinite.mp (fun hi => hn ⟨h, hh, hi⟩)
  have hinsert : insert Y H ∈ B :=
    ⟨ad_insert_orthogonal hm.1.1 (hQ Y hY) ho, insert_subset hY hm.1.2⟩
  have hYH : Y ∈ H := hm.2 hinsert (subset_insert _ _) (by simp)
  exact hQ Y hY (by simpa using ho Y hYH)

/-- A remainder may be empty or finite; U records its local ground set. -/
def Remainder (F : Set (Set X)) (U : Set X) (H : Set (Set X)) : Prop :=
  ADFamily H ∧ (∀ h ∈ H, h ⊆ U) ∧ H ⊆ Orthogonal F ∧
    ∀ Y ⊆ U, Y.Infinite → Y ∈ Orthogonal F → ∃ h ∈ H, (Y ∩ h).Infinite

theorem exists_remainder (F : Set (Set X)) (U : Set X) : ∃ H, Remainder F U H := by
  let Q : Set (Set X) := {Y | Y.Infinite ∧ Y ⊆ U ∧ Y ∈ Orthogonal F}
  obtain ⟨H, hH, hHQ, hm⟩ := exists_relative_maximal Q (fun _ h => h.1)
  exact ⟨H, hH, fun h hh => (hHQ hh).2.1, fun h hh => (hHQ hh).2.2,
    fun Y hYU hY ho => hm Y ⟨hY, hYU, ho⟩⟩

lemma ad_union_orthogonal {F H : Set (Set X)} (hF : ADFamily F)
    (hH : ADFamily H) (ho : H ⊆ Orthogonal F) : ADFamily (F ∪ H) := by
  constructor
  · intro a ha
    exact ha.elim (hF.1 a) (hH.1 a)
  · intro a ha b hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hF.2 a ha b hb hab
    · simpa [inter_comm] using ho hb a ha
    · exact ho ha b hb
    · exact hH.2 a ha b hb hab

lemma remainder_maximalOn {F H : Set (Set X)} {U : Set X}
    (hF : ADFamily F) (hFU : ∀ a ∈ F, a ⊆ U) (hH : Remainder F U H) :
    MaximalOn (F ∪ H) U := by
  refine ⟨ad_union_orthogonal hF hH.1 hH.2.2.1, ?_, ?_⟩
  · intro a ha; exact ha.elim (hFU a) (hH.2.1 a)
  · intro Y hYU hY
    by_cases ho : Y ∈ Orthogonal F
    · obtain ⟨a, ha, hi⟩ := hH.2.2.2 Y hYU hY ho
      exact ⟨a, Or.inr ha, hi⟩
    · have hex : ∃ a ∈ F, (Y ∩ a).Infinite := by
        by_contra hn
        exact ho (fun a ha => not_infinite.mp (fun hi => hn ⟨a, ha, hi⟩))
      obtain ⟨a, ha, hi⟩ := hex
      exact ⟨a, Or.inl ha, hi⟩

lemma remainder_iff_completion {F H : Set (Set X)} {U : Set X}
    (hH : ADFamily H) (hHU : ∀ h ∈ H, h ⊆ U) (ho : H ⊆ Orthogonal F)
    (hF : ADFamily F) (hFU : ∀ a ∈ F, a ⊆ U) :
    Remainder F U H ↔ MaximalOn (F ∪ H) U := by
  refine ⟨remainder_maximalOn hF hFU, ?_⟩
  intro hm
  refine ⟨hH, hHU, ho, ?_⟩
  intro Y hYU hY hYo
  obtain ⟨a, ha, hi⟩ := hm.2.2 Y hYU hY
  rcases ha with ha | ha
  · exact False.elim (hi (hYo a ha))
  · exact ⟨a, ha, hi⟩

/-- Paper equation (4.1), hence exact preservation of admissible remainders. -/
theorem remainder_orthogonal_invariance {F P : Set (Set X)}
    (h : Orthogonal F = Orthogonal P) (U : Set X) (H : Set (Set X)) :
    Remainder F U H ↔ Remainder P U H := by
  simp only [Remainder, h]

def remainderCardinals (F : Set (Set X)) (U : Set X) : Set Cardinal :=
  {κ | ∃ H, Remainder F U H ∧ #H = κ}

noncomputable def extensionCost (F : Set (Set X)) (U : Set X) : Cardinal :=
  sInf (remainderCardinals F U)

lemma remainderCardinals_nonempty (F : Set (Set X)) (U : Set X) :
    (remainderCardinals F U).Nonempty := by
  obtain ⟨H, hH⟩ := exists_remainder F U
  exact ⟨#H, H, hH, rfl⟩

lemma exists_minimum_remainder (F : Set (Set X)) (U : Set X) :
    ∃ H, Remainder F U H ∧ #H = extensionCost F U :=
  csInf_mem (remainderCardinals_nonempty F U)

lemma extensionCost_le {F H : Set (Set X)} {U : Set X} (h : Remainder F U H) :
    extensionCost F U ≤ #H := csInf_le' ⟨H, h, rfl⟩

/-- Paper equation (4.2), valid for zero and finite extension costs too. -/
theorem extensionCost_orthogonal_invariance {F P : Set (Set X)}
    (h : Orthogonal F = Orthogonal P) (U : Set X) :
    extensionCost F U = extensionCost P U := by
  unfold extensionCost remainderCardinals
  simp only [remainder_orthogonal_invariance h U]

lemma extensionCost_eq_zero_of_maximal {F : Set (Set X)} {U : Set X}
    (hm : MaximalOn F U) : extensionCost F U = 0 := by
  apply le_antisymm ?_ zero_le
  have hr : Remainder F U ∅ := by
    refine ⟨⟨by simp, by simp⟩, by simp, empty_subset _, ?_⟩
    intro Y hYU hY ho
    obtain ⟨a, ha, hi⟩ := hm.2.2 Y hYU hY
    exact False.elim (hi (ho a ha))
  simpa using extensionCost_le hr

end InfinitaryCombinatorics.Formalizations.R0

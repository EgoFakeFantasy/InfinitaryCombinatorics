import Formalizations.R0.CountableCompletion
import Formalizations.R0.LocalGlobal

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

lemma remainder_of_completion {F G : Set (Set X)} {U : Set X}
    (hG : MaximalOn G U) (hFG : F ⊆ G) : Remainder F U (G \ F) := by
  refine ⟨hG.1.mono diff_subset, fun h hh => hG.2.1 h hh.1, ?_, ?_⟩
  · intro h hh a ha
    exact hG.1.2 h hh.1 a (hFG ha) (fun heq => hh.2 (heq ▸ ha))
  · intro Y hYU hY ho
    obtain ⟨a, ha, hi⟩ := hG.2.2 Y hYU hY
    exact ⟨a, ⟨ha, fun haF => hi (ho a haF)⟩, hi⟩

lemma maximalOn_embedding {Y : Type} (e : X ↪ Y) {F : Set (Set X)} {U : Set X}
    (hF : MaximalOn F U) : MaximalOn (Set.image e '' F) (e '' U) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro a ⟨b, hb, rfl⟩; exact (hF.1.1 b hb).image e.injective.injOn
    · rintro a ⟨b, hb, rfl⟩ c ⟨d, hd, rfl⟩ hac
      rw [← Set.image_inter e.injective]
      exact (hF.1.2 b hb d hd (fun h => hac (h ▸ rfl))).image e
  · rintro a ⟨b, hb, rfl⟩; exact image_mono (hF.2.1 b hb)
  · intro Z hZU hZ
    have hp : (e ⁻¹' Z).Infinite := hZ.preimage (by
      intro z hz; obtain ⟨x, _, hx⟩ := hZU hz; exact ⟨x, hx⟩)
    have hsub : e ⁻¹' Z ⊆ U := by
      intro x hx
      obtain ⟨u, hu, hux⟩ := hZU hx
      exact e.injective hux ▸ hu
    obtain ⟨a, ha, hia⟩ := hF.2.2 (e ⁻¹' Z) hsub hp
    refine ⟨e '' a, ⟨a, ha, rfl⟩, ?_⟩
    apply (hia.image e.injective.injOn).mono
    rintro _ ⟨x, ⟨hxZ, hxa⟩, rfl⟩
    exact ⟨hxZ, ⟨x, hxa, rfl⟩⟩

lemma countable_local_extensionCost_le [Countable X] {F : Set (Set X)} {U : Set X}
    (hF : ADFamily F) (hFC : F.Countable) (hFU : ∀ a ∈ F, a ⊆ U) (hU : U.Infinite) :
    extensionCost F U ≤ almostDisjointnessNumber := by
  classical
  letI : Infinite U := hU.to_subtype
  let e : U ↪ X := ⟨Subtype.val, Subtype.val_injective⟩
  let F' : Set (Set U) := (fun a => e ⁻¹' a) '' F
  have hF' : ADFamily F' := by
    constructor
    · rintro p ⟨a, ha, rfl⟩
      exact (hF.1 a ha).preimage (fun x hx => ⟨⟨x, hFU a ha hx⟩, rfl⟩)
    · rintro p ⟨a, ha, rfl⟩ q ⟨b, hb, rfl⟩ hpq
      have hf := hF.2 a ha b hb (fun h => hpq (h ▸ rfl))
      simpa only [preimage_inter] using hf.preimage (f := e) e.injective.injOn
  obtain ⟨G, hFG, hG, hGc⟩ := countable_completion hF' (hFC.image (fun a => e ⁻¹' a))
  let G' : Set (Set X) := Set.image e '' G
  have hrange : e '' (Set.univ : Set U) = U := by ext x; simp [e]
  have hG' : MaximalOn G' U := by
    simpa only [hrange] using maximalOn_embedding e hG
  have hFG' : F ⊆ G' := by
    intro a ha
    refine ⟨e ⁻¹' a, hFG ⟨a, ha, rfl⟩, ?_⟩
    exact image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hFU a ha hx⟩, rfl⟩)
  calc
    extensionCost F U ≤ #(G' \ F : Set (Set X)) := extensionCost_le (remainder_of_completion hG' hFG')
    _ ≤ #G' := Cardinal.mk_le_mk_of_subset diff_subset
    _ ≤ #G := Cardinal.mk_image_le
    _ ≤ almostDisjointnessNumber := hGc

def incidence (E : Set (Set X)) (n : Set X) : Set (Set X) :=
  {a | a ∈ E ∧ (a ∩ n).Infinite}

def CountableIncidence (E N : Set (Set X)) : Prop :=
  ∀ n ∈ N, (incidence E n).Countable

lemma restriction_countable_of_incidence {E : Set (Set X)} {n : Set X}
    (h : (incidence E n).Countable) : (restriction E n).Countable := by
  apply (h.image (fun a => a ∩ n)).mono
  rintro p ⟨hi, a, ha, rfl⟩
  exact ⟨a, ⟨ha, hi⟩, rfl⟩

lemma extensionCost_le_of_countable_incidence [Countable X]
    {E N : Set (Set X)} (hE : ADFamily E) (hN : MAD N) (hinc : CountableIncidence E N) :
    extensionCost E univ ≤ max #N almostDisjointnessNumber := by
  apply extensionCost_le_of_local_bound E hN
  intro n hn
  exact countable_local_extensionCost_le (restriction_ad hE n)
    (restriction_countable_of_incidence (hinc n hn)) (fun _ hp => restriction_subset hp)
    (hN.1.2.1 n hn)

lemma union_card_eq_max {E H : Set (Set X)} (hE : E.Infinite) :
    #(E ∪ H : Set (Set X)) = max #E #H := by
  have hω : ℵ₀ ≤ #E := Cardinal.aleph0_le_mk_iff.mpr hE.to_subtype
  apply le_antisymm
  · exact (Cardinal.mk_union_le E H).trans_eq (Cardinal.add_eq_max hω)
  · exact max_le (Cardinal.mk_le_mk_of_subset subset_union_left)
      (Cardinal.mk_le_mk_of_subset subset_union_right)

lemma minimum_cost_completion {E : Set (Set X)} (hE : _root_.R0.AlmostDisjoint E) :
    ∃ K, E ⊆ K ∧ MAD K ∧ #K = max #E (extensionCost E univ) := by
  obtain ⟨H, hH, hcard⟩ := exists_minimum_remainder E univ
  have hm := remainder_maximalOn hE.2 (fun _ _ => subset_univ _) hH
  refine ⟨E ∪ H, subset_union_left, mad_iff_infinite_maximalOn.mpr
    ⟨hE.1.mono subset_union_left, hm⟩, ?_⟩
  rw [union_card_eq_max hE.1, hcard]

/-- Paper Corollary 6.3: exact original inclusion and exact size a. -/
theorem countable_incidence_transfer [Countable X] [Infinite X]
    {E N : Set (Set X)} (hE : _root_.R0.AlmostDisjoint E)
    (hEc : #E ≤ almostDisjointnessNumber) (hN : MAD N)
    (hNc : #N = almostDisjointnessNumber) (hinc : CountableIncidence E N) :
    ∃ K, E ⊆ K ∧ MAD K ∧ #K = almostDisjointnessNumber := by
  have he : extensionCost E univ ≤ almostDisjointnessNumber := by
    simpa only [hNc, max_self] using extensionCost_le_of_countable_incidence hE.2 hN hinc
  obtain ⟨K, hEK, hK, hcard⟩ := minimum_cost_completion hE
  exact ⟨K, hEK, hK, le_antisymm (hcard.le.trans (max_le hEc he)) (mad_card_lower hK)⟩

theorem nonFinIntersecting_countable_incidence_transfer [Countable X] [Infinite X]
    {E N : Set (Set X)} (hE : _root_.R0.AlmostDisjoint E)
    (hEc : #E ≤ almostDisjointnessNumber) (hN : MAD N)
    (hNc : #N = almostDisjointnessNumber) (hinc : CountableIncidence E N)
    (hnot : ¬ _root_.R0.FinIntersecting E) :
    ∃ K, E ⊆ K ∧ MAD K ∧ #K = almostDisjointnessNumber ∧ ¬ _root_.R0.FinIntersecting K := by
  obtain ⟨K, hEK, hK, hcard⟩ := countable_incidence_transfer hE hEc hN hNc hinc
  exact ⟨K, hEK, hK, hcard, not_finIntersecting_of_subset hnot hEK⟩

end InfinitaryCombinatorics.Formalizations.R0

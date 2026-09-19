import Formalizations.R0.Remainder

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

def restriction (F : Set (Set X)) (U : Set X) : Set (Set X) :=
  {p | p.Infinite ∧ ∃ a ∈ F, p = a ∩ U}

lemma restriction_subset {F : Set (Set X)} {U p : Set X} (hp : p ∈ restriction F U) :
    p ⊆ U := by
  obtain ⟨_, a, _, rfl⟩ := hp
  exact inter_subset_right

lemma restriction_ad {F : Set (Set X)} (hF : ADFamily F) (U : Set X) :
    ADFamily (restriction F U) := by
  refine ⟨fun _ hp => hp.1, ?_⟩
  rintro p ⟨_, a, ha, rfl⟩ q ⟨_, b, hb, rfl⟩ hpq
  exact (hF.2 a ha b hb (fun h => hpq (h ▸ rfl))).subset
    (fun _ hx => ⟨hx.1.1, hx.2.1⟩)

lemma restriction_card_le (F : Set (Set X)) (U : Set X) : #(restriction F U) ≤ #F := by
  calc
    #(restriction F U) ≤ #((fun a => a ∩ U) '' F) := Cardinal.mk_le_mk_of_subset (by
      rintro p ⟨_, a, ha, rfl⟩; exact ⟨a, ha, rfl⟩)
    _ ≤ #F := Cardinal.mk_image_le

lemma orthogonal_mono_set {F : Set (Set X)} {Y Z : Set X}
    (hY : Y ∈ Orthogonal F) (hZY : Z ⊆ Y) : Z ∈ Orthogonal F :=
  fun a ha => (hY a ha).subset (inter_subset_inter_left _ hZY)

lemma orthogonal_restriction {F : Set (Set X)} {U Y : Set X} (hYU : Y ⊆ U) :
    Y ∈ Orthogonal (restriction F U) ↔ Y ∈ Orthogonal F := by
  constructor
  · intro h a ha
    by_cases hai : (a ∩ U).Infinite
    · have hf := h (a ∩ U) ⟨hai, a, ha, rfl⟩
      exact hf.subset (fun _ hx => ⟨hx.1, hx.2, hYU hx.1⟩)
    · exact (not_infinite.mp hai).subset (fun _ hx => ⟨hx.2, hYU hx.1⟩)
  · intro h p hp
    obtain ⟨_, a, ha, rfl⟩ := hp
    exact (h a ha).subset (fun _ hx => ⟨hx.1, hx.2.1⟩)

lemma restrict_remainder {F H : Set (Set X)} (hH : Remainder F univ H) (U : Set X) :
    Remainder (restriction F U) U (restriction H U) := by
  refine ⟨restriction_ad hH.1 U, fun _ hp => restriction_subset hp, ?_, ?_⟩
  · intro p hp
    apply (orthogonal_restriction (restriction_subset hp)).mpr
    obtain ⟨_, a, ha, rfl⟩ := hp
    exact orthogonal_mono_set (hH.2.2.1 ha) inter_subset_left
  · intro Y hYU hY ho
    obtain ⟨a, ha, hi⟩ := hH.2.2.2 Y (subset_univ _) hY
      ((orthogonal_restriction hYU).mp ho)
    have hai : (a ∩ U).Infinite := hi.mono (fun _ hx => ⟨hx.2, hYU hx.1⟩)
    exact ⟨a ∩ U, ⟨hai, a, ha, rfl⟩,
      hi.mono (fun _ hx => ⟨hx.1, hx.2, hYU hx.1⟩)⟩

/-- The lower local bound includes finite and empty local restriction families. -/
theorem extensionCost_restriction_le (F : Set (Set X)) (U : Set X) :
    extensionCost (restriction F U) U ≤ extensionCost F univ := by
  obtain ⟨H, hH, hcard⟩ := exists_minimum_remainder F univ
  exact (extensionCost_le (restrict_remainder hH U)).trans
    ((restriction_card_le H U).trans_eq hcard)

lemma assemble_remainders {F N : Set (Set X)} (hN : MAD N)
    (H : N → Set (Set X)) (hH : ∀ n, Remainder (restriction F n.val) n.val (H n)) :
    Remainder F univ (⋃ n, H n) := by
  refine ⟨?_, fun _ _ => subset_univ _, ?_, ?_⟩
  · constructor
    · intro p hp
      obtain ⟨n, hp⟩ := mem_iUnion.mp hp
      exact (hH n).1.1 p hp
    · intro p hp q hq hpq
      obtain ⟨n, hp⟩ := mem_iUnion.mp hp
      obtain ⟨m, hq⟩ := mem_iUnion.mp hq
      by_cases hnm : n = m
      · subst m; exact (hH n).1.2 p hp q hq hpq
      · exact (hN.1.2.2 n n.property m m.property (fun h => hnm (Subtype.ext h))).subset
          (inter_subset_inter ((hH n).2.1 p hp) ((hH m).2.1 q hq))
  · intro p hp
    obtain ⟨n, hp⟩ := mem_iUnion.mp hp
    exact (orthogonal_restriction ((hH n).2.1 p hp)).mp ((hH n).2.2.1 hp)
  · intro Y _ hY ho
    obtain ⟨n, hn, hi⟩ := hN.2 Y hY
    have hYo : Y ∩ n ∈ Orthogonal (restriction F n) :=
      (orthogonal_restriction inter_subset_right).mpr (orthogonal_mono_set ho inter_subset_left)
    obtain ⟨p, hp, hip⟩ := (hH ⟨n, hn⟩).2.2.2 (Y ∩ n) inter_subset_right hi hYo
    exact ⟨p, mem_iUnion.mpr ⟨⟨n, hn⟩, hp⟩,
      hip.mono (fun _ hx => ⟨hx.1.1, hx.2⟩)⟩

/-- Paper Theorem 6.2, both inequalities with the actual attained cost. -/
theorem local_to_global_extension_bounds (F : Set (Set X)) {N : Set (Set X)} (hN : MAD N) :
    (⨆ n : N, extensionCost (restriction F n.val) n.val) ≤ extensionCost F univ ∧
    extensionCost F univ ≤ max #N (⨆ n : N, extensionCost (restriction F n.val) n.val) := by
  refine ⟨ciSup_le' (fun n => extensionCost_restriction_le F n.val), ?_⟩
  choose H hH hcard using fun n : N => exists_minimum_remainder (restriction F n.val) n.val
  have hω : ℵ₀ ≤ #N := Cardinal.aleph0_le_mk_iff.mpr hN.1.1.to_subtype
  calc
    extensionCost F univ ≤ #(⋃ n, H n) := extensionCost_le (assemble_remainders hN H hH)
    _ ≤ #N * ⨆ n : N, #(H n) := Cardinal.mk_iUnion_le H
    _ = #N * ⨆ n : N, extensionCost (restriction F n.val) n.val := by
      congr 1
      exact congrArg iSup (funext hcard)
    _ ≤ max #N (⨆ n : N, extensionCost (restriction F n.val) n.val) :=
      Cardinal.mul_le_max_of_aleph0_le_left hω

lemma extensionCost_le_of_local_bound (F : Set (Set X)) {N : Set (Set X)} (hN : MAD N)
    {κ : Cardinal} (hlocal : ∀ n ∈ N, extensionCost (restriction F n) n ≤ κ) :
    extensionCost F univ ≤ max #N κ :=
  (local_to_global_extension_bounds F hN).2.trans
    (max_le_max le_rfl (ciSup_le' (fun n => hlocal n n.property)))

end InfinitaryCombinatorics.Formalizations.R0

import Formalizations.R0.CountableParts

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

def madCardinals : Set Cardinal := {κ | ∃ M : Set (Set ℕ), MAD M ∧ #M = κ}

noncomputable def almostDisjointnessNumber : Cardinal := sInf madCardinals

lemma madCardinals_nonempty : madCardinals.Nonempty := by
  obtain ⟨M, hM, _, _⟩ := uniform_nonFinIntersecting_mad
  exact ⟨#M, M, hM, rfl⟩

lemma exists_minimum_mad_nat :
    ∃ M : Set (Set ℕ), MAD M ∧ #M = almostDisjointnessNumber :=
  csInf_mem madCardinals_nonempty

lemma almostDisjointnessNumber_le {M : Set (Set ℕ)} (hM : MAD M) :
    almostDisjointnessNumber ≤ #M := csInf_le' ⟨M, hM, rfl⟩

lemma aleph0_le_almostDisjointnessNumber : ℵ₀ ≤ almostDisjointnessNumber := by
  obtain ⟨M, hM, hcard⟩ := exists_minimum_mad_nat
  rw [← hcard]
  exact Cardinal.aleph0_le_mk_iff.mpr hM.1.1.to_subtype

lemma mad_card_lower {X : Type} [Countable X] [Infinite X] {M : Set (Set X)} (hM : MAD M) :
    almostDisjointnessNumber ≤ #M := by
  let e : X ≃ ℕ := Classical.choice inferInstance
  have h := almostDisjointnessNumber_le (mad_image e hM)
  simpa only [Cardinal.mk_image_eq e.injective.image_injective] using h

lemma exists_minimum_mad (X : Type) [Countable X] [Infinite X] :
    ∃ M : Set (Set X), MAD M ∧ #M = almostDisjointnessNumber := by
  obtain ⟨M, hM, hcard⟩ := exists_minimum_mad_nat
  let e : ℕ ≃ X := Classical.choice inferInstance
  exact ⟨Set.image e '' M, mad_image e hM,
    (Cardinal.mk_image_eq e.injective.image_injective).trans hcard⟩

variable {X : Type}

lemma finite_completion {F : Set (Set X)} (hF : ADFamily F) (hf : F.Finite) :
    ∃ G, F ⊆ G ∧ G.Finite ∧ MaximalOn G univ := by
  classical
  let c : Set X := univ \ ⋃₀ F
  have ho : c ∈ Orthogonal F := by
    intro a ha
    apply finite_empty.subset
    intro x hx
    exact False.elim (hx.1.2 ⟨a, ha, hx.2⟩)
  by_cases hc : c.Infinite
  · refine ⟨insert c F, subset_insert _ _, hf.insert c, ?_⟩
    apply finite_cover_maximalOn (ad_insert_orthogonal hF hc ho) (hf.insert c)
      (fun _ _ => subset_univ _) ?_
    apply finite_empty.subset
    intro x hx
    by_cases hxu : x ∈ ⋃₀ F
    · obtain ⟨a, ha, hxa⟩ := hxu
      exact False.elim (hx.2 ⟨a, Or.inr ha, hxa⟩)
    · exact False.elim (hx.2 ⟨c, by simp, mem_univ _, hxu⟩)
  · exact ⟨F, Subset.rfl, hf,
      finite_cover_maximalOn hF hf (fun _ _ => subset_univ _) (not_infinite.mp hc)⟩

/-- The infinite-input case of paper Lemma 6.1. The extension contains the
original sets exactly, after pulling back and correcting the selected members. -/
theorem countable_infinite_mad_extension [Countable X] [Infinite X]
    {F : Set (Set X)} (hF : ADFamily F) (hFC : F.Countable) (hFI : F.Infinite) :
    ∃ K, F ⊆ K ∧ MAD K ∧ #K = almostDisjointnessNumber := by
  classical
  letI : Countable F := hFC.to_subtype
  letI : Infinite F := hFI.to_subtype
  let ef : ℕ ≃ F := Classical.choice inferInstance
  let f : ℕ → Set X := fun n => (ef n).val
  have hfi : Function.Injective f := fun _ _ h => ef.injective (Subtype.ext h)
  obtain ⟨L, hL, hLc⟩ := exists_minimum_mad X
  let el : ℕ ↪ L := Set.Infinite.natEmbedding L hL.1.1
  let g : ℕ → Set X := fun n => (el n).val
  have hgi : Function.Injective g := fun _ _ h => el.injective (Subtype.ext h)
  obtain ⟨e, he⟩ := exists_equiv_almostMatching f g
    (fun n => hF.1 _ (ef n).property)
    (fun n => hL.1.2.1 _ (el n).property)
    (fun n m hnm => hF.2 _ (ef n).property _ (ef m).property (fun h => hnm (hfi h)))
    (fun n m hnm => hL.1.2.2 _ (el n).property _ (el m).property (fun h => hnm (hgi h)))
  let L' : Set (Set X) := Set.image e.symm '' L
  have hL' : MAD L' := mad_image e.symm hL
  have hL'c : #L' = almostDisjointnessNumber :=
    (Cardinal.mk_image_eq e.symm.injective.image_injective).trans hLc
  let l : ℕ → L' := fun n => ⟨e.symm '' g n, g n, (el n).property, rfl⟩
  have hli : Function.Injective l := by
    intro n m h
    apply hgi
    apply e.symm.injective.image_injective
    exact congrArg Subtype.val h
  have hl (n : ℕ) : AlmostEqual (l n).val (f n) := by
    simpa only [l, Equiv.image_symm_eq_preimage] using he n
  let change : L' → Set X := fun a =>
    if h : ∃ n, l n = a then f (Classical.choose h) else a.val
  have hchange (a : L') : AlmostEqual (change a) a.val := by
    dsimp only [change]
    split
    next h =>
      have hp := (hl (Classical.choose h)).symm
      simpa only [Classical.choose_spec h] using hp
    next h => exact AlmostEqual.refl a.val
  have hselected (n : ℕ) : change (l n) = f n := by
    have hex : ∃ m, l m = l n := ⟨n, rfl⟩
    dsimp only [change]
    rw [dif_pos hex]
    exact congrArg f (hli (Classical.choose_spec hex))
  obtain ⟨hK, hKc⟩ := finite_change_mad hL' change hchange
  refine ⟨range change, ?_, hK, hKc.trans hL'c⟩
  intro a ha
  let n : ℕ := ef.symm ⟨a, ha⟩
  have hfn : f n = a := congrArg Subtype.val (ef.apply_symm_apply ⟨a, ha⟩)
  exact ⟨l n, (hselected n).trans hfn⟩

/-- Paper Lemma 6.1, with finite maximal completions allowed for finite input. -/
theorem countable_completion [Countable X] [Infinite X]
    {F : Set (Set X)} (hF : ADFamily F) (hFC : F.Countable) :
    ∃ K, F ⊆ K ∧ MaximalOn K univ ∧ #K ≤ almostDisjointnessNumber := by
  classical
  by_cases hi : F.Infinite
  · obtain ⟨K, hFK, hK, hcard⟩ := countable_infinite_mad_extension hF hFC hi
    exact ⟨K, hFK, (mad_iff_infinite_maximalOn.mp hK).2, hcard.le⟩
  · obtain ⟨K, hFK, hf, hK⟩ := finite_completion hF (not_infinite.mp hi)
    exact ⟨K, hFK, hK,
      (Cardinal.le_aleph0_iff_set_countable.mpr hf.countable).trans aleph0_le_almostDisjointnessNumber⟩

end InfinitaryCombinatorics.Formalizations.R0

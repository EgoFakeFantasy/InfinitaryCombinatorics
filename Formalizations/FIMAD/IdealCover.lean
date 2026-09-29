import Formalizations.FIMAD.PositiveExtension

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set
open InfinitaryCombinatorics.Formalizations.R0 (blocksOver finite_trace_of_finite)

lemma finite_family_homogeneous {F : Set (Set ℕ)} (hF : F.Finite)
    {I : Set ℕ} (hI : I.Infinite) :
    ∃ J ⊆ I, J.Infinite ∧ ∀ s ∈ F, J ⊆ s ∨ Disjoint J s := by
  classical
  induction F, hF using Set.Finite.induction_on generalizing I with
  | empty => exact ⟨I, Subset.rfl, hI, by simp⟩
  | @insert s F hs hF ih =>
    obtain ⟨J, hJI, hJ, hJF⟩ := ih hI
    have restrict (K : Set ℕ) (hKJ : K ⊆ J) :
        ∀ t ∈ F, K ⊆ t ∨ Disjoint K t := by
      intro t ht
      rcases hJF t ht with h | h
      · exact Or.inl (hKJ.trans h)
      · exact Or.inr (h.mono_left hKJ)
    by_cases h : (J ∩ s).Infinite
    · refine ⟨J ∩ s, inter_subset_left.trans hJI, h, ?_⟩
      intro t ht
      rcases ht with rfl | ht
      · exact Or.inl inter_subset_right
      · exact restrict _ inter_subset_left t ht
    · have hd : (J \ s).Infinite := by simpa [diff_inter] using hJ.diff (not_infinite.mp h)
      refine ⟨J \ s, diff_subset.trans hJI, hd, ?_⟩
      intro t ht
      rcases ht with rfl | ht
      · exact Or.inr disjoint_sdiff_left
      · exact restrict _ diff_subset t ht

/-- A block union in the generated ideal gives an FI witness, for the
entire AD family, including members outside the finite covering subfamily. -/
theorem ideal_block_cover_witness {A : Set (Set ℕ)} (hA : ADFamily A)
    (C : R0.FinSequence ℕ) {I : Set ℕ} (hI : I.Infinite)
    (hcover : InIdeal A (blocksOver C I)) :
    ∃ J ⊆ I, J.Infinite ∧ R0.Centered (R0.retainedTraces C A J) := by
  classical
  obtain ⟨F, hF, hFA, hcover⟩ := hcover
  let U : Set ℕ := ⋃ a ∈ F, a
  let E := blocksOver C I \ U
  have hE : E.Finite := hcover
  let I' := I \ R0.trace C E
  have hI' : I'.Infinite := hI.diff (finite_trace_of_finite C hE)
  have hblock (n) (hn : n ∈ I') : C.block n ⊆ U := by
    intro x hx
    by_contra hxu
    exact hn.2 ⟨x, ⟨mem_iUnion₂.mpr ⟨n, hn.1, hx⟩, hxu⟩, hx⟩
  obtain ⟨J, hJI', hJ, hhom⟩ := finite_family_homogeneous (hF.image (R0.trace C)) hI'
  have houtside (a) (ha : a ∈ A) (haF : a ∉ F) : (J ∩ R0.trace C a).Finite := by
    have hfin : (a ∩ U).Finite := by
      have hf := hF.biUnion fun b hb => hA.2 a ha b (hFA hb)
        (show a ≠ b from fun h => haF (h ▸ hb))
      apply hf.subset
      rintro x ⟨hxa, hxU⟩
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hxU
      exact mem_iUnion₂.mpr ⟨b, hb, hxa, hxb⟩
    apply (finite_trace_of_finite C hfin).subset
    rintro n ⟨hn, x, hxa, hxn⟩
    exact ⟨x, ⟨hxa, hblock n (hJI' hn) hxn⟩, hxn⟩
  have heq (t) (ht : t ∈ R0.retainedTraces C A J) : t = J := by
    obtain ⟨ht, a, ha, rfl⟩ := ht
    have haF : a ∈ F := by
      by_contra hn
      exact ht (houtside a ha hn)
    rcases hhom _ ⟨a, haF, rfl⟩ with h | h
    · exact inter_eq_left.mpr h
    · exact False.elim (ht (h.inter_eq ▸ finite_empty))
  refine ⟨J, hJI'.trans diff_subset, hJ, ?_⟩
  intro G hG hf hne
  apply hJ.mono
  intro n hn
  apply mem_iInter₂.mpr
  intro t ht
  exact heq t (hG ht) ▸ hn

lemma trace_infinite_of_infinite_inter_blocks (C : R0.FinSequence ℕ)
    {a S : Set ℕ} (h : (a ∩ blocksOver C S).Infinite) :
    (S ∩ R0.trace C a).Infinite := by
  intro hf
  apply h
  apply (hf.biUnion fun n _ => C.finite n).subset
  rintro x ⟨hxa, hxS⟩
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hxS
  exact mem_iUnion₂.mpr ⟨n, ⟨hn, x, hxa, hxn⟩, hxn⟩

end InfinitaryCombinatorics.Formalizations.FIMAD

import R0.Basic

namespace R0
open Set

lemma centered_of_cofinite {T : Set (Set ℕ)} {i : Set ℕ} (hi : i.Infinite)
    (h : ∀ t ∈ T, (i \ t).Finite) : Centered T := by
  intro F hFT hF _
  have hbad : (⋃ t ∈ F, i \ t).Finite :=
    hF.biUnion fun t ht => h t (hFT ht)
  apply (hi.diff hbad).mono
  intro n hn
  simp only [mem_iInter]
  intro t ht
  by_contra hnt
  exact hn.2 (by simp only [mem_iUnion]; exact ⟨t, ht, hn.1, hnt⟩)

/-- The lower-bound argument does not require almost disjointness. -/
theorem finIntersecting_of_nonsplitting_traces {X : Type*} (A : Set (Set X))
    (h : ∀ C : FinSequence X, ¬ Splitting (trace C '' A)) : FinIntersecting A := by
  intro C
  have hn := h C
  unfold Splitting at hn
  push Not at hn
  obtain ⟨i, hi, hn⟩ := hn
  refine ⟨i, hi, centered_of_cofinite hi ?_⟩
  intro t ht
  obtain ⟨htInf, a, ha, rfl⟩ := ht
  have hn' := hn (trace C a) (mem_image_of_mem _ ha)
  have hf : (i \ trace C a).Finite := by
    by_contra hfin
    exact hn' ⟨htInf, hfin⟩
  simpa [diff_inter] using hf

end R0

import Formalizations.R0.BinarySplitting

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

noncomputable def branch (s : Set ℕ) : Set Node := range (node s)

theorem branch_infinite (s : Set ℕ) : (branch s).Infinite :=
  infinite_range_of_injective (node_injective s)

lemma branch_eq_halves (s : Set ℕ) : branch s = half s false ∪ half s true := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    by_cases hn : n ∈ s
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n, hn, rfl⟩
  · rintro (⟨n, _, rfl⟩ | ⟨n, _, rfl⟩) <;> exact ⟨n, rfl⟩

lemma branch_inter_finite {s t : Set ℕ} (hst : s ≠ t) :
    (branch s ∩ branch t).Finite := by
  rw [branch_eq_halves, branch_eq_halves]
  rw [union_inter_distrib_right, inter_union_distrib_left, inter_union_distrib_left]
  exact ((half_inter_of_ne hst false false).union (half_inter_of_ne hst false true)).union
    ((half_inter_of_ne hst true false).union (half_inter_of_ne hst true true))

lemma branch_injective : Function.Injective branch := by
  intro s t h
  by_contra hst
  have hf := branch_inter_finite hst
  rw [h, inter_self] at hf
  exact branch_infinite t hf

noncomputable def allBranches : Set (Set Node) := range branch

lemma allBranches_ad : _root_.R0.AlmostDisjoint allBranches := by
  refine ⟨infinite_range_of_injective branch_injective, ?_, ?_⟩
  · rintro a ⟨s, rfl⟩; exact branch_infinite s
  · rintro a ⟨s, rfl⟩ b ⟨t, rfl⟩ hab
    exact branch_inter_finite (fun h => hab (h ▸ rfl))

lemma allBranches_card : #allBranches = 2 ^ ℵ₀ := by
  rw [allBranches, Cardinal.mk_range_eq _ branch_injective]
  simp

lemma trace_branch (s : Set ℕ) : trace treeBlocks (branch s) = (Set.univ : Set ℕ) := by
  apply eq_univ_of_forall
  intro n
  exact ⟨node s n, ⟨n, rfl⟩, node_mem_level s n⟩

/-- Bijection transport also preserves maximality, including finite local families. -/
lemma maximalOn_image {X Y : Type} (e : X ≃ Y) {F : Set (Set X)} {U : Set X}
    (hF : MaximalOn F U) : MaximalOn (Set.image e '' F) (e '' U) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro a ⟨b, hb, rfl⟩
      exact (hF.1.1 b hb).image e.injective.injOn
    · rintro a ⟨b, hb, rfl⟩ c ⟨d, hd, rfl⟩ hac
      rw [← Set.image_inter e.injective]
      exact (hF.1.2 b hb d hd (fun h => hac (h ▸ rfl))).image e
  · rintro a ⟨b, hb, rfl⟩
    exact image_mono (hF.2.1 b hb)
  · intro Z hZU hZ
    have hp : (e ⁻¹' Z).Infinite := hZ.preimage (by simp)
    have hsub : e ⁻¹' Z ⊆ U := by
      intro x hx
      obtain ⟨u, hu, hux⟩ := hZU hx
      exact e.injective hux ▸ hu
    obtain ⟨a, ha, hia⟩ := hF.2.2 (e ⁻¹' Z) hsub hp
    refine ⟨e '' a, ⟨a, ha, rfl⟩, ?_⟩
    apply (hia.image e.injective.injOn).mono
    rintro _ ⟨x, ⟨hxZ, hxa⟩, rfl⟩
    exact ⟨hxZ, ⟨x, hxa, rfl⟩⟩

lemma mad_image {X Y : Type} (e : X ≃ Y) {F : Set (Set X)} (hF : MAD F) :
    MAD (Set.image e '' F) := by
  apply mad_iff_infinite_maximalOn.mpr
  refine ⟨hF.1.1.image e.injective.image_injective.injOn, ?_⟩
  simpa using maximalOn_image e (mad_iff_infinite_maximalOn.mp hF).2

/-- Paper Theorem 5.1 on the countable tree model. Completion is obtained by
Zorn, an equivalent classical choice of a maximal extension of all branches. -/
theorem uniform_nonFinIntersecting_mad_tree :
    ∃ K : Set (Set Node), MAD K ∧ #K = 2 ^ ℵ₀ ∧ ¬ FinIntersecting K := by
  classical
  obtain ⟨M, hBM, hM⟩ := exists_mad_extension allBranches_ad
  have hcard : #M = 2 ^ ℵ₀ := by
    apply le_antisymm
    · calc
        #M ≤ #(Set Node) := Cardinal.mk_set_le M
        _ = 2 ^ ℵ₀ := by simp
    · rw [← allBranches_card]
      exact Cardinal.mk_le_mk_of_subset hBM
  let S : Set Node → Set ℕ := Function.invFun branch
  have hTS : TraceSplitCondition allBranches treeBlocks S := by
    intro I hI
    obtain ⟨s, hs⟩ := exists_splitter hI
    refine ⟨branch s, ⟨s, rfl⟩, ?_⟩
    have hs' : S (branch s) = s := Function.leftInverse_invFun branch_injective s
    simpa [trace_branch, hs', inter_assoc, diff_eq] using hs
  obtain ⟨K, hK, hKM, hnot⟩ := trace_splitting_replacement hM hBM treeBlocks S hTS
  exact ⟨K, hK, hKM.trans hcard, hnot⟩

/-- A uniform ZFC MAD example of size continuum on the original ground set Nat. -/
theorem uniform_nonFinIntersecting_mad :
    ∃ K : Set (Set ℕ), MAD K ∧ #K = 2 ^ ℵ₀ ∧ ¬ FinIntersecting K := by
  obtain ⟨K, hK, hcard, hnot⟩ := uniform_nonFinIntersecting_mad_tree
  refine ⟨Set.image nodeEquivNat '' K, mad_image nodeEquivNat hK, ?_, ?_⟩
  · exact (Cardinal.mk_image_eq nodeEquivNat.injective.image_injective).trans hcard
  · exact (finIntersecting_equiv nodeEquivNat K).not.mpr hnot

end InfinitaryCombinatorics.Formalizations.R0

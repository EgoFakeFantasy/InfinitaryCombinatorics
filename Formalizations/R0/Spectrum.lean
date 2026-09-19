import Formalizations.R0.UniformMAD

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

noncomputable def regularCode (s : Set ℕ) : Set ℕ :=
  range (fun n : ℕ => 3 * n) ∪ (fun n : ℕ => 3 * n + 1) '' s

lemma regularCode_regular (s : Set ℕ) :
    (regularCode s).Infinite ∧ (regularCode s)ᶜ.Infinite := by
  constructor
  · apply (infinite_range_of_injective (f := fun n : ℕ => 3 * n) (by intro n m h; dsimp only at *; omega)).mono
    exact subset_union_left
  · apply (infinite_range_of_injective (f := fun n : ℕ => 3 * n + 2) (by intro n m h; dsimp only at *; omega)).mono
    rintro x ⟨n, rfl⟩ (⟨m, hm⟩ | ⟨m, _, hm⟩) <;> (dsimp only at *; omega)

lemma regularCode_injective : Function.Injective regularCode := by
  intro s t h
  have hmem (s : Set ℕ) (n : ℕ) : 3 * n + 1 ∈ regularCode s ↔ n ∈ s := by
    constructor
    · rintro (⟨m, hm⟩ | ⟨m, hm, heq⟩)
      · dsimp only at *; omega
      · have : m = n := by dsimp only at *; omega
        exact this ▸ hm
    · intro hn
      exact Or.inr ⟨n, hn, rfl⟩
  ext n
  rw [← hmem s n, h, hmem t n]

lemma regular_sets_card : #{s : Set ℕ | s.Infinite ∧ sᶜ.Infinite} = 2 ^ ℵ₀ := by
  apply le_antisymm
  · exact (Cardinal.mk_set_le _).trans_eq (by simp)
  · have hsub : range regularCode ⊆ {s : Set ℕ | s.Infinite ∧ sᶜ.Infinite} := by
      rintro s ⟨t, rfl⟩
      exact regularCode_regular t
    have hc := Cardinal.mk_le_mk_of_subset hsub
    rw [Cardinal.mk_range_eq _ regularCode_injective] at hc
    simpa using hc

lemma exists_regular_splitting_of_card {κ : Cardinal}
    (hlo : splittingNumber ≤ κ) (hhi : κ ≤ 2 ^ ℵ₀) :
    ∃ S : Set (Set ℕ), Splitting S ∧ #S = κ ∧ ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite := by
  obtain ⟨S, hS, hcS, hrS⟩ := exists_minimal_regular_splitting
  obtain ⟨T, hT, hcT⟩ := Cardinal.le_mk_iff_exists_subset.mp (hhi.trans_eq regular_sets_card.symm)
  refine ⟨S ∪ T, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨s, hs, hsplit⟩ := hS I hI
    exact ⟨s, Or.inl hs, hsplit⟩
  · apply le_antisymm
    · calc
        #(S ∪ T : Set (Set ℕ)) ≤ #S + #T := Cardinal.mk_union_le S T
        _ = max splittingNumber κ := by rw [hcS, hcT, Cardinal.add_eq_max aleph0_le_splittingNumber]
        _ = κ := max_eq_right hlo
    · rw [← hcT]
      exact Cardinal.mk_le_mk_of_subset subset_union_right
  · intro s hs
    rcases hs with hs | hs
    · exact hrS s hs
    · exact hT hs

lemma treeFamily_card_eq {S : Set (Set ℕ)} (hS : Splitting S)
    (hreg : ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite) : #(treeFamily S) = #S := by
  apply le_antisymm (treeFamily_card_le hS)
  let f : S → treeFamily S := fun s => ⟨half s.val false, ⟨(s, false), rfl⟩⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro s t heq
  apply Subtype.ext
  by_contra hst
  have hf := half_inter_of_ne hst false false
  have hv : half s.val false = half t.val false := congrArg Subtype.val heq
  rw [hv, inter_self] at hf
  exact half_infinite (hreg t.val t.property).1 (hreg t.val t.property).2 false hf

/-- Paper Corollary 3.4: every and only cardinal in the closed interval [s,c]
is the size of a non-fin-intersecting infinite almost disjoint family on Nat. -/
theorem nonFinIntersecting_cardinal_spectrum (κ : Cardinal) :
    (∃ A : Set (Set ℕ), AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = κ) ↔
      splittingNumber ≤ κ ∧ κ ≤ 2 ^ ℵ₀ := by
  constructor
  · rintro ⟨A, _, hnot, rfl⟩
    exact ⟨splittingNumber_le_of_not_finIntersecting hnot,
      (Cardinal.mk_set_le A).trans_eq (by simp)⟩
  · rintro ⟨hlo, hhi⟩
    obtain ⟨S, hS, hc, hr⟩ := exists_regular_splitting_of_card hlo hhi
    let e := nodeEquivNat.toEmbedding
    refine ⟨Set.image e '' treeFamily S, almostDisjoint_map e (treeFamily_almostDisjoint hS hr),
      not_finIntersecting_map e (treeFamily_not_finIntersecting hS), ?_⟩
    exact (Cardinal.mk_image_eq e.injective.image_injective).trans ((treeFamily_card_eq hS hr).trans hc)

end InfinitaryCombinatorics.Formalizations.R0

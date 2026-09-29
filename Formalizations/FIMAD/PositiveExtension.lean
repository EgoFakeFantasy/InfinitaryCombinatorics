import Formalizations.FIMAD.Nonexistence
import InfinitaryCombinatorics.CountableSplitting

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set

lemma positive_diff_finite_union_infinite {A : Set (Set ℕ)} {Y : Set ℕ}
    (hY : ¬ InIdeal A Y) {F : Set (Set ℕ)} (hF : F.Finite) (hFA : F ⊆ A) :
    (Y \ ⋃ a ∈ F, a).Infinite := by
  intro hf
  exact hY ⟨F, hF, hFA, hf⟩

/-- The extension lemma used at every countable stage of the CH construction.
All positive requirements are met infinitely, while every old member is met finitely. -/
theorem countable_positive_extension {A Y : Set (Set ℕ)}
    (hA : R0.AlmostDisjoint A) (hcA : A.Countable) (hcY : Y.Countable)
    (hY : ∀ y ∈ Y, ¬ InIdeal A y) :
    ∃ a : Set ℕ, a.Infinite ∧ (∀ b ∈ A, (a ∩ b).Finite) ∧
      ∀ y ∈ Y, (a ∩ y).Infinite := by
  classical
  obtain ⟨e, he⟩ := hcA.exists_eq_range hA.1.nonempty
  have hYe : (insert univ Y).Nonempty := ⟨univ, mem_insert _ _⟩
  obtain ⟨v, hv⟩ := (hcY.insert univ).exists_eq_range hYe
  have hvpos (j) : ¬ InIdeal A (v j) := by
    have hj : v j ∈ insert univ Y := hv ▸ mem_range_self j
    rcases hj with hj | hj
    · rw [hj]
      exact ideal_proper_of_infinite_ad hA
    · exact hY _ hj
  have hx (n j : ℕ) : ∃ x, n ≤ x ∧ x ∈ v j ∧ ∀ i ≤ n, x ∉ e i := by
    let F := e '' {i | i ≤ n}
    have hF : F.Finite := (finite_le_nat n).image e
    have hFA : F ⊆ A := by
      rintro _ ⟨i, _, rfl⟩
      exact he ▸ mem_range_self i
    obtain ⟨x, hx, hn⟩ := infinite_tail_point (positive_diff_finite_union_infinite (hvpos j) hF hFA) n
    refine ⟨x, hn, hx.1, ?_⟩
    intro i hi hxi
    exact hx.2 (mem_iUnion₂.mpr ⟨e i, ⟨i, hi, rfl⟩, hxi⟩)
  choose x hxn hxv hxe using hx
  let a : Set ℕ := ⋃ n : ℕ, x n '' {j | j ≤ n}
  have ha (n j : ℕ) (hj : j ≤ n) : x n j ∈ a :=
    mem_iUnion.mpr ⟨n, j, hj, rfl⟩
  have hmeet (j) : (a ∩ v j).Infinite := by
    intro hf
    obtain ⟨K, hK⟩ := hf.bddAbove
    let n := max j (K + 1)
    have hb := hK (show x n j ∈ a ∩ v j from ⟨ha n j (le_max_left _ _), hxv n j⟩)
    have hn := hxn n j
    have hk : K + 1 ≤ n := le_max_right _ _
    omega
  refine ⟨a, (hmeet 0).mono inter_subset_left, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, rfl⟩ := he.symm ▸ hb
    apply ((finite_lt_nat i).biUnion (fun n _ => (finite_le_nat n).image (x n))).subset
    rintro z ⟨hz, hzb⟩
    obtain ⟨n, j, hj, rfl⟩ := mem_iUnion.mp hz
    have hni : n < i := by
      by_contra hh
      exact hxe n j i (Nat.le_of_not_gt hh) hzb
    exact mem_iUnion₂.mpr ⟨n, hni, j, hj, rfl⟩
  · intro y hy
    obtain ⟨j, rfl⟩ := hv.symm ▸ mem_insert_of_mem univ hy
    exact hmeet j

lemma infinite_inIdeal_meets_member {A : Set (Set ℕ)} {X : Set ℕ}
    (hX : X.Infinite) (hi : InIdeal A X) : ∃ a ∈ A, (X ∩ a).Infinite := by
  classical
  obtain ⟨F, hF, hFA, hcover⟩ := hi
  by_contra hn
  push Not at hn
  have hf : (⋃ a ∈ F, X ∩ a).Finite := hF.biUnion fun a ha => hn a (hFA ha)
  apply hX
  apply (hcover.union hf).subset
  intro x hx
  by_cases hh : x ∈ ⋃ a ∈ F, a
  · obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hh
    exact Or.inr (mem_iUnion₂.mpr ⟨a, ha, hx, hxa⟩)
  · exact Or.inl ⟨hx, hh⟩

end InfinitaryCombinatorics.Formalizations.FIMAD

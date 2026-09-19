import Formalizations.R0.BinaryCoding

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

variable {X H : Type} (C : FinSequence X) (f : H → ℕ → X)
  (hf : ∀ h n, f h n ∈ C.block n)

include hf

lemma selector_index_eq {h k : H} {n m : ℕ} (heq : f h n = f k m) : n = m := by
  by_contra hne
  exact Set.disjoint_left.mp (C.disjoint n m hne) (hf h n) (heq.symm ▸ hf k m)

lemma selector_injective (h : H) : Function.Injective (f h) := by
  intro n m heq
  exact selector_index_eq C f hf heq

lemma selector_trace (h : H) (U : Set ℕ) : trace C (f h '' U) = U := by
  ext n
  constructor
  · rintro ⟨x, ⟨m, hm, rfl⟩, hx⟩
    have heq : m = n := by
      by_contra hne
      exact Set.disjoint_left.mp (C.disjoint m n hne) (hf h m) hx
    exact heq ▸ hm
  · intro hn
    exact ⟨f h n, ⟨n, hn, rfl⟩, hf h n⟩

lemma selector_block_subsingleton (h : H) (U : Set ℕ) (n : ℕ) :
    (f h '' U ∩ C.block n).Subsingleton := by
  rintro x ⟨⟨i, _, rfl⟩, hi⟩ y ⟨⟨j, _, rfl⟩, hj⟩
  have hei : i = n := by
    by_contra hne
    exact Set.disjoint_left.mp (C.disjoint i n hne) (hf h i) hi
  have hej : j = n := by
    by_contra hne
    exact Set.disjoint_left.mp (C.disjoint j n hne) (hf h j) hj
  rw [hei, hej]

lemma selector_inter_finite {h k : H}
    (hev : ∃ N, ∀ n, N ≤ n → f h n ≠ f k n) (U V : Set ℕ) :
    (f h '' U ∩ f k '' V).Finite := by
  obtain ⟨N, hN⟩ := hev
  apply ((Finset.range N).finite_toSet.image (f h)).subset
  rintro x ⟨⟨n, _, rfl⟩, m, _, hm⟩
  have hnm : n = m := selector_index_eq C f hf hm.symm
  subst m
  refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
  by_contra hn
  exact hN n (by omega) hm.symm

/-- The reusable selector form of the exact trace lemma. The same branch may
carry several almost disjoint supports; different branches separate eventually. -/
theorem selector_realization
    (hev : ∀ h k, h ≠ k → ∃ N, ∀ n, N ≤ n → f h n ≠ f k n)
    (U : H → Set (Set ℕ)) (hU : ∀ h, ADFamily (U h)) :
    let A : ((h : H) × U h) → Set X := fun p => f p.1 '' p.2.val
    Function.Injective A ∧ ADFamily (range A) ∧
      ∀ p, trace C (A p) = p.2.val ∧ A p ⊆ ⋃ n, C.block n ∧
        ∀ n, (A p ∩ C.block n).Subsingleton := by
  classical
  dsimp only
  let A : ((h : H) × U h) → Set X := fun p => f p.1 '' p.2.val
  have hinf (p : (h : H) × U h) : (A p).Infinite :=
    (hU p.1).1 p.2.val p.2.property |>.image (selector_injective C f hf p.1).injOn
  have hpair (p q : (h : H) × U h) (hpq : p ≠ q) : (A p ∩ A q).Finite := by
    rcases p with ⟨h, u⟩
    rcases q with ⟨k, v⟩
    by_cases hhk : h = k
    · subst k
      have huv : u.val ≠ v.val := by
        intro huv
        apply hpq
        have he : u = v := Subtype.ext huv
        subst v
        rfl
      dsimp [A]
      rw [← Set.image_inter (selector_injective C f hf h)]
      exact ((hU h).2 _ u.property _ v.property huv).image (f h)
    · exact selector_inter_finite C f hf (hev h k hhk) _ _
  have hinj : Function.Injective A := by
    intro p q heq
    by_contra hpq
    have hh := hpair p q hpq
    rw [heq, inter_self] at hh
    exact hinf q hh
  refine ⟨hinj, ⟨?_, ?_⟩, ?_⟩
  · rintro a ⟨p, rfl⟩
    exact hinf p
  · rintro a ⟨p, rfl⟩ b ⟨q, rfl⟩ hab
    exact hpair p q (fun h => hab (h ▸ rfl))
  · intro p
    refine ⟨selector_trace C f hf _ _, ?_, selector_block_subsingleton C f hf _ _⟩
    rintro x ⟨n, _, rfl⟩
    exact mem_iUnion.mpr ⟨n, hf p.1 n⟩

end InfinitaryCombinatorics.Formalizations.R0

import Formalizations.R0.Local

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

def binaryParts (a D : Set X) : Set (Set X) :=
  {p | p.Infinite ∧ (p = a ∩ D ∨ p = a \ D)}

lemma binaryParts_finite (a D : Set X) : (binaryParts a D).Finite := by
  have hf : ({a ∩ D, a \ D} : Set (Set X)).Finite := by simp
  apply hf.subset
  intro p hp
  simpa only [mem_insert_iff, mem_singleton_iff] using hp.2

lemma binaryParts_maximalOn (a D : Set X) :
    MaximalOn (binaryParts a D) a := by
  have had : ADFamily (binaryParts a D) := by
    refine ⟨fun _ hp => hp.1, ?_⟩
    intro p hp q hq hpq
    rcases hp.2 with rfl | rfl <;> rcases hq.2 with rfl | rfl
    · exact False.elim (hpq rfl)
    · apply finite_empty.subset
      intro x hx
      exact False.elim (hx.2.2 hx.1.2)
    · apply finite_empty.subset
      intro x hx
      exact False.elim (hx.1.2 hx.2.2)
    · exact False.elim (hpq rfl)
  refine ⟨had, ?_, ?_⟩
  · intro p hp
    rcases hp.2 with rfl | rfl
    · exact inter_subset_left
    · exact diff_subset
  · intro Y hYa hY
    by_cases h0 : (Y ∩ D).Infinite
    · refine ⟨a ∩ D, ⟨h0.mono (inter_subset_inter_left _ hYa), Or.inl rfl⟩, ?_⟩
      exact h0.mono (fun _ hx => ⟨hx.1, hYa hx.1, hx.2⟩)
    · have h1 : (Y \ D).Infinite := by
        simpa [diff_inter] using hY.diff (not_infinite.mp h0)
      refine ⟨a \ D, ⟨h1.mono (diff_subset_diff_left hYa), Or.inr rfl⟩, ?_⟩
      exact h1.mono (fun _ hx => ⟨hx.1, hYa hx.1, hx.2⟩)

lemma binary_refinement_mad {M : Set (Set X)} (hM : MAD M) (D : Set X → Set X) :
    MAD (refinement M (fun a => binaryParts a (D a))) ∧
      #(refinement M (fun a => binaryParts a (D a))) = #M := by
  have hp : ∀ a ∈ M, MaximalOn (binaryParts a (D a)) a :=
    fun a _ => binaryParts_maximalOn a _
  exact ⟨refinement_mad hM hp,
    finite_refinement_card hM.1 hp (fun a _ => binaryParts_finite a (D a))⟩

def blocksOver (C : _root_.R0.FinSequence X) (S : Set ℕ) : Set X :=
  ⋃ n ∈ S, C.block n

lemma mem_blocksOver_of_mem_block (C : _root_.R0.FinSequence X)
    {S : Set ℕ} {x : X} {n : ℕ} (hx : x ∈ C.block n) :
    x ∈ blocksOver C S ↔ n ∈ S := by
  constructor
  · intro h
    obtain ⟨m, hm, hxm⟩ := mem_iUnion₂.mp h
    by_cases hmn : m = n
    · exact hmn ▸ hm
    · exact False.elim (Set.disjoint_left.mp (C.disjoint m n hmn) hxm hx)
  · intro hn
    exact mem_iUnion₂.mpr ⟨n, hn, hx⟩

lemma trace_inter_blocksOver (C : _root_.R0.FinSequence X) (a : Set X) (S : Set ℕ) :
    _root_.R0.trace C (a ∩ blocksOver C S) = _root_.R0.trace C a ∩ S := by
  ext n
  constructor
  · rintro ⟨x, ⟨hxa, hxS⟩, hxn⟩
    exact ⟨⟨x, hxa, hxn⟩, (mem_blocksOver_of_mem_block C hxn).mp hxS⟩
  · rintro ⟨⟨x, hxa, hxn⟩, hn⟩
    exact ⟨x, ⟨hxa, (mem_blocksOver_of_mem_block C hxn).mpr hn⟩, hxn⟩

lemma trace_diff_blocksOver (C : _root_.R0.FinSequence X) (a : Set X) (S : Set ℕ) :
    _root_.R0.trace C (a \ blocksOver C S) = _root_.R0.trace C a \ S := by
  ext n
  constructor
  · rintro ⟨x, ⟨hxa, hxS⟩, hxn⟩
    exact ⟨⟨x, hxa, hxn⟩, fun hn => hxS ((mem_blocksOver_of_mem_block C hxn).mpr hn)⟩
  · rintro ⟨⟨x, hxa, hxn⟩, hn⟩
    exact ⟨x, ⟨hxa, fun h => hn ((mem_blocksOver_of_mem_block C hxn).mp h)⟩, hxn⟩

lemma infinite_of_trace_infinite (C : _root_.R0.FinSequence X) {a : Set X}
    (ht : (_root_.R0.trace C a).Infinite) : a.Infinite := by
  classical
  letI : Infinite (_root_.R0.trace C a) := ht.to_subtype
  have hw (n : _root_.R0.trace C a) : ∃ x, x ∈ a ∧ x ∈ C.block n := n.property
  choose f hf using hw
  apply Set.infinite_of_injective_forall_mem (f := f) ?_ (fun n => (hf n).1)
  intro n m h
  apply Subtype.ext
  by_contra hnm
  exact Set.disjoint_left.mp (C.disjoint n m hnm) (hf n).2 (h ▸ (hf m).2)

lemma finite_trace_of_finite (C : _root_.R0.FinSequence X) {a : Set X}
    (ha : a.Finite) : (_root_.R0.trace C a).Finite := by
  by_contra h
  exact infinite_of_trace_infinite C (not_finite.mp h) ha

/-- The splitters are fixed before the universal quantifier over I. -/
def TraceSplitCondition (D : Set (Set X)) (C : _root_.R0.FinSequence X)
    (S : Set X → Set ℕ) : Prop :=
  ∀ I : Set ℕ, I.Infinite → ∃ a ∈ D,
    (I ∩ (_root_.R0.trace C a ∩ S a)).Infinite ∧
    (I ∩ (_root_.R0.trace C a \ S a)).Infinite

/-- Paper Theorem 7.1. Finite pieces are excluded by binaryParts itself. -/
theorem trace_splitting_replacement {M D : Set (Set X)} (hM : MAD M) (hDM : D ⊆ M)
    (C : _root_.R0.FinSequence X) (S : Set X → Set ℕ)
    (hTS : TraceSplitCondition D C S) :
    ∃ K : Set (Set X), MAD K ∧ #K = #M ∧ ¬ _root_.R0.FinIntersecting K := by
  classical
  let cut : Set X → Set X := fun a => if a ∈ D then blocksOver C (S a) else ∅
  let K := refinement M (fun a => binaryParts a (cut a))
  obtain ⟨hK, hcard⟩ := binary_refinement_mad hM cut
  refine ⟨K, hK, hcard, not_finIntersecting_of_split_traces K C ?_⟩
  intro I hI
  obtain ⟨a, ha, h0, h1⟩ := hTS I hI
  have ht0 : _root_.R0.trace C (a ∩ cut a) = _root_.R0.trace C a ∩ S a :=
    by simpa [cut, ha] using trace_inter_blocksOver C a (S a)
  have ht1 : _root_.R0.trace C (a \ cut a) = _root_.R0.trace C a \ S a :=
    by simpa [cut, ha] using trace_diff_blocksOver C a (S a)
  have hi0 : (a ∩ cut a).Infinite := infinite_of_trace_infinite C
    (ht0.symm ▸ h0.mono inter_subset_right)
  have hi1 : (a \ cut a).Infinite := infinite_of_trace_infinite C
    (ht1.symm ▸ h1.mono inter_subset_right)
  refine ⟨a ∩ cut a, mem_refinement.mpr ⟨a, hDM ha, hi0, Or.inl rfl⟩,
    a \ cut a, mem_refinement.mpr ⟨a, hDM ha, hi1, Or.inr rfl⟩, ?_⟩
  rw [ht0, ht1]
  refine ⟨h0, h1, Set.disjoint_left.mpr ?_⟩
  intro n hn hm
  exact hm.2.2 hn.2.2

/-- Paper Proposition 7.2: maximality implies hitting, without block coverage. -/
theorem mad_trace_hitting {M : Set (Set X)} (hM : MAD M)
    (C : _root_.R0.FinSequence X) {I : Set ℕ} (hI : I.Infinite) :
    ∃ a ∈ M, (I ∩ _root_.R0.trace C a).Infinite := by
  have ht : _root_.R0.trace C (blocksOver C I) = I := by
    ext n
    constructor
    · rintro ⟨x, hxI, hxn⟩
      exact (mem_blocksOver_of_mem_block C hxn).mp hxI
    · intro hn
      obtain ⟨x, hx⟩ := C.nonempty n
      exact ⟨x, (mem_blocksOver_of_mem_block C hx).mpr hn, hx⟩
  obtain ⟨a, ha, hi⟩ := hM.2 (blocksOver C I)
    (infinite_of_trace_infinite C (ht.symm ▸ hI))
  refine ⟨a, ha, ?_⟩
  by_contra hn
  have hf : (I ∩ _root_.R0.trace C a).Finite := not_infinite.mp hn
  apply hi
  apply (hf.biUnion (fun n _ => C.finite n)).subset
  rintro x ⟨hxI, hxa⟩
  obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hxI
  exact mem_iUnion₂.mpr ⟨n, ⟨hn, x, hxa, hxn⟩, hxn⟩

/-- The hypothesis concerns distinct indexed members, not just distinct trace values. -/
theorem no_trace_splitting_of_pairwise_finite {D : Set (Set X)}
    (C : _root_.R0.FinSequence X) (S : Set X → Set ℕ)
    (hpair : ∀ a ∈ D, ∀ b ∈ D, a ≠ b →
      (_root_.R0.trace C a ∩ _root_.R0.trace C b).Finite) :
    ¬ TraceSplitCondition D C S := by
  intro hTS
  obtain ⟨a, ha, h0, _⟩ := hTS univ infinite_univ
  have hI : (_root_.R0.trace C a ∩ S a).Infinite := by simpa using h0
  obtain ⟨b, hb, hb0, hb1⟩ := hTS (_root_.R0.trace C a ∩ S a) hI
  by_cases hab : a = b
  · subst b
    apply hb1
    apply finite_empty.subset
    intro n hn
    exact False.elim (hn.2.2 hn.1.2)
  · exact hb0 ((hpair a ha b hb hab).subset (fun _ hx => ⟨hx.1.1, hx.2.1⟩))

end InfinitaryCombinatorics.Formalizations.R0

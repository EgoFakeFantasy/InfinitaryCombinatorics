import R0.LowerBound
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace R0
open Set Cardinal

lemma Splits.of_subset {s i j : Set ℕ} (h : Splits s j) (hji : j ⊆ i) :
    Splits s i := by
  exact ⟨h.1.mono (inter_subset_inter_left _ hji),
    h.2.mono (fun _ hx => ⟨hji hx.1, hx.2⟩)⟩

lemma finite_family_unsplit (F : Set (Set ℕ)) (hF : F.Finite) :
    ∀ i : Set ℕ, i.Infinite → ∃ j ⊆ i, j.Infinite ∧ ∀ s ∈ F, ¬ Splits s j := by
  induction F, hF using Set.Finite.induction_on with
  | empty =>
      intro i hi
      exact ⟨i, Subset.rfl, hi, by simp⟩
  | @insert s F hs hF ih =>
      intro i hi
      obtain ⟨j, hji, hj, hnj⟩ := ih i hi
      by_cases hjs : (j ∩ s).Infinite
      · refine ⟨j ∩ s, inter_subset_left.trans hji, hjs, ?_⟩
        intro t ht hsp
        rcases mem_insert_iff.mp ht with hts | ht
        · subst t
          have hempty : (j ∩ s) \ s = ∅ := by ext n; simp
          exact hsp.2 (hempty ▸ finite_empty)
        · exact hnj t ht (hsp.of_subset inter_subset_left)
      · have hd : (j \ s).Infinite := by
          have hfin : (j ∩ s).Finite := not_infinite.mp hjs
          simpa [diff_inter] using hj.diff hfin
        refine ⟨j \ s, diff_subset.trans hji, hd, ?_⟩
        intro t ht hsp
        rcases mem_insert_iff.mp ht with hts | ht
        · subst t
          have hempty : (j \ s) ∩ s = ∅ := by ext n; simp
          exact hsp.1 (hempty ▸ finite_empty)
        · exact hnj t ht (hsp.of_subset diff_subset)

lemma Splitting.infinite {S : Set (Set ℕ)} (hS : Splitting S) : S.Infinite := by
  intro hF
  obtain ⟨j, _, hj, hn⟩ := finite_family_unsplit S hF univ infinite_univ
  obtain ⟨s, hs, hsp⟩ := hS j hj
  exact hn s hs hsp

lemma exists_splitter {i : Set ℕ} (hi : i.Infinite) : ∃ s, Splits s i := by
  classical
  let e : ℕ ↪ i := hi.natEmbedding i
  let evenPart : ℕ → ℕ := fun n => (e (2 * n)).val
  let oddPart : ℕ → ℕ := fun n => (e (2 * n + 1)).val
  have hev : Function.Injective evenPart := by
    intro n m h
    have h' : 2 * n = 2 * m := e.injective (Subtype.ext h)
    omega
  have hod : Function.Injective oddPart := by
    intro n m h
    have h' : 2 * n + 1 = 2 * m + 1 := e.injective (Subtype.ext h)
    omega
  refine ⟨range evenPart, ?_, ?_⟩
  · apply (infinite_range_of_injective hev).mono
    rintro x ⟨n, rfl⟩
    exact ⟨(e (2 * n)).property, mem_range_self _⟩
  · apply (infinite_range_of_injective hod).mono
    rintro x ⟨n, rfl⟩
    refine ⟨(e (2 * n + 1)).property, ?_⟩
    rintro ⟨m, hm⟩
    have h' : 2 * m = 2 * n + 1 := e.injective (Subtype.ext hm)
    omega

lemma splitting_univ : Splitting (univ : Set (Set ℕ)) := by
  intro i hi
  obtain ⟨s, hs⟩ := exists_splitter hi
  exact ⟨s, mem_univ _, hs⟩

def splittingCardinals : Set Cardinal :=
  {κ | ∃ S : Set (Set ℕ), Splitting S ∧ #S = κ}

noncomputable def splittingNumber : Cardinal := sInf splittingCardinals

lemma splittingCardinals_nonempty : splittingCardinals.Nonempty :=
  ⟨#(univ : Set (Set ℕ)), univ, splitting_univ, rfl⟩

lemma splittingNumber_le {S : Set (Set ℕ)} (hS : Splitting S) : splittingNumber ≤ #S :=
  csInf_le' ⟨S, hS, rfl⟩

lemma exists_minimal_splitting :
    ∃ S : Set (Set ℕ), Splitting S ∧ #S = splittingNumber :=
  csInf_mem splittingCardinals_nonempty

/-- Corral-Rodrigues' lower bound, proved from the definitions. -/
theorem finIntersecting_of_card_lt {X : Type} (A : Set (Set X))
    (hA : #A < splittingNumber) : FinIntersecting A := by
  apply finIntersecting_of_nonsplitting_traces
  intro C hS
  have hle : splittingNumber ≤ #A :=
    (splittingNumber_le hS).trans Cardinal.mk_image_le
  exact (not_le_of_gt hA) hle

lemma splittingNumber_le_of_not_finIntersecting {X : Type} {A : Set (Set X)}
    (hA : ¬ FinIntersecting A) : splittingNumber ≤ #A := by
  apply le_of_not_gt
  intro hlt
  exact hA (finIntersecting_of_card_lt A hlt)

end R0

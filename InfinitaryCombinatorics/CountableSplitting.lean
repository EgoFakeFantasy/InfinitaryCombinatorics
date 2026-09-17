import R0.Main
import Mathlib.Data.Set.Countable

/-!
# Every countable family leaves an infinite set unsplit

Let `S : Set (Set ℕ)` be countable. Then there is an infinite `I : Set ℕ` such
that no member of `S` splits `I` (with `R0.Splits s i` meaning that both
`i ∩ s` and `i \ s` are infinite). Consequently `ℵ₀ < R0.splittingNumber`.

The proof is the diagonal argument. One first builds a decreasing sequence
`splitBranch A n` of infinite sets such that `splitBranch A (n+1)` is either
contained in `A n` or disjoint from it; a strictly increasing selector
`splitPick A n ∈ splitBranch A n` then gives an infinite `I` with
`I \ splitBranch A n` finite for every `n`, so `A n` cannot split `I`.
-/

namespace InfinitaryCombinatorics

open Set
open Cardinal

/-- An infinite set of naturals is unbounded. -/
lemma infinite_exists_gt {s : Set ℕ} (hs : s.Infinite) (a : ℕ) : ∃ b ∈ s, a < b := by
  classical
  by_contra h
  have hbound : s ⊆ {x : ℕ | x ≤ a} := by
    intro x hx
    exact le_of_not_gt (fun hxa => h ⟨x, hx, hxa⟩)
  have hfin : s.Finite :=
    (Finset.range (a + 1)).finite_toSet.subset (by
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound hx)))
  exact (not_infinite.mpr hfin) hs

/-- One thinning step. Given an infinite `b`, `splitStep` returns an infinite
subset of `b` which lies either inside `A n` or entirely outside it. -/
lemma splitStep_exists (A : ℕ → Set ℕ) (n : ℕ) {b : Set ℕ} (hb : b.Infinite) :
    ∃ c : Set ℕ, c ⊆ b ∧ c.Infinite ∧ (c ⊆ A n ∨ Disjoint c (A n)) := by
  classical
  by_cases h : (b ∩ A n).Infinite
  · exact ⟨b ∩ A n, inter_subset_left, h, Or.inl inter_subset_right⟩
  · have hfin : (b ∩ A n).Finite := not_infinite.mp h
    have hd : (b \ A n).Infinite := by
      have h' : (b \ (b ∩ A n)).Infinite := hb.diff hfin
      exact h'.mono (by
        rintro x hx
        exact ⟨hx.1, fun hxA => hx.2 ⟨hx.1, hxA⟩⟩)
    exact ⟨b \ A n, diff_subset, hd,
      Or.inr (disjoint_left.2 (by
        intro x hx hxA
        exact hx.2 hxA))⟩

noncomputable def splitStep (A : ℕ → Set ℕ) (n : ℕ) (b : Set ℕ) (hb : b.Infinite) :
    Set ℕ :=
  Classical.choose (splitStep_exists A n hb)

lemma splitStep_spec (A : ℕ → Set ℕ) (n : ℕ) (b : Set ℕ) (hb : b.Infinite) :
    splitStep A n b hb ⊆ b ∧ (splitStep A n b hb).Infinite ∧
      (splitStep A n b hb ⊆ A n ∨ Disjoint (splitStep A n b hb) (A n)) :=
  Classical.choose_spec (splitStep_exists A n hb)

/-- The decreasing sequence of infinite sets, carrying its infinitude witness
along so that the recursion stays structural. -/
noncomputable def splitBranchAux (A : ℕ → Set ℕ) : ℕ → {s : Set ℕ // s.Infinite}
  | 0 => ⟨(univ : Set ℕ), by simpa using (infinite_univ : (univ : Set ℕ).Infinite)⟩
  | n + 1 =>
      let p := splitBranchAux A n
      let c := splitStep A n p.1 p.2
      ⟨c, (splitStep_spec A n p.1 p.2).2.1⟩

noncomputable def splitBranch (A : ℕ → Set ℕ) (n : ℕ) : Set ℕ :=
  (splitBranchAux A n).1

lemma splitBranch_infinite (A : ℕ → Set ℕ) (n : ℕ) : (splitBranch A n).Infinite :=
  (splitBranchAux A n).2

lemma splitBranch_succ (A : ℕ → Set ℕ) (n : ℕ) :
    splitBranch A (n + 1) = splitStep A n (splitBranch A n) (splitBranch_infinite A n) :=
  rfl

lemma splitBranch_succ_subset (A : ℕ → Set ℕ) (n : ℕ) :
    splitBranch A (n + 1) ⊆ splitBranch A n := by
  rw [splitBranch_succ]
  exact (splitStep_spec A n (splitBranch A n) (splitBranch_infinite A n)).1

lemma splitBranch_succ_decides (A : ℕ → Set ℕ) (n : ℕ) :
    splitBranch A (n + 1) ⊆ A n ∨ Disjoint (splitBranch A (n + 1)) (A n) := by
  rw [splitBranch_succ]
  exact (splitStep_spec A n (splitBranch A n) (splitBranch_infinite A n)).2.2

lemma splitBranch_antitone (A : ℕ → Set ℕ) (m n : ℕ) (hmn : m ≤ n) :
    splitBranch A n ⊆ splitBranch A m := by
  revert m
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rfl
  | succ n ih =>
      intro m hm
      by_cases h : m ≤ n
      · exact (splitBranch_succ_subset A n).trans (ih m h)
      · have hm' : m = n + 1 := by omega
        subst m
        rfl

/-- A strictly increasing selector with `splitPick A n ∈ splitBranch A n`. -/
noncomputable def splitPick (A : ℕ → Set ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => Classical.choose (infinite_exists_gt (splitBranch_infinite A (n + 1)) (splitPick A n))

lemma splitPick_mem (A : ℕ → Set ℕ) (n : ℕ) : splitPick A n ∈ splitBranch A n := by
  cases n with
  | zero => simp [splitPick, splitBranch, splitBranchAux]
  | succ n =>
      simpa [splitPick] using
        (Classical.choose_spec
          (infinite_exists_gt (splitBranch_infinite A (n + 1)) (splitPick A n))).1

lemma splitPick_lt_succ (A : ℕ → Set ℕ) (n : ℕ) : splitPick A n < splitPick A (n + 1) := by
  simpa [splitPick] using
    (Classical.choose_spec
      (infinite_exists_gt (splitBranch_infinite A (n + 1)) (splitPick A n))).2

lemma splitPick_strictMono (A : ℕ → Set ℕ) : StrictMono (splitPick A) :=
  strictMono_nat_of_lt_succ (splitPick_lt_succ A)

lemma pickRange_infinite (A : ℕ → Set ℕ) : (range (splitPick A)).Infinite :=
  infinite_range_of_injective (splitPick_strictMono A).injective

/-- The selected range is a pseudo-intersection of the branch sequence. -/
lemma pickRange_diff_splitBranch_finite (A : ℕ → Set ℕ) (n : ℕ) :
    (range (splitPick A) \ splitBranch A n).Finite := by
  let B : Finset ℕ := Finset.range n
  refine (B.finite_toSet.image (splitPick A)).subset ?_
  rintro x ⟨⟨k, rfl⟩, hxnot⟩
  by_cases hlt : k < n
  · exact ⟨k, Finset.mem_range.mpr hlt, rfl⟩
  · exact False.elim
      (hxnot ((splitBranch_antitone A n k (le_of_not_gt hlt)) (splitPick_mem A k)))

/-- Diagonal lemma: for every sequence `A : ℕ → Set ℕ` there is an infinite set
that no `A n` splits. -/
theorem exists_unsplit_of_sequence (A : ℕ → Set ℕ) :
    ∃ i : Set ℕ, i.Infinite ∧ ∀ n : ℕ, ¬ R0.Splits (A n) i := by
  refine ⟨range (splitPick A), pickRange_infinite A, ?_⟩
  intro n hsp
  have hfin := pickRange_diff_splitBranch_finite A (n + 1)
  rcases splitBranch_succ_decides A n with hsub | hdisj
  · have hsmall : range (splitPick A) \ A n ⊆ range (splitPick A) \ splitBranch A (n + 1) := by
      rintro x ⟨hxi, hxnot⟩
      exact ⟨hxi, fun hxB => hxnot (hsub hxB)⟩
    exact (not_infinite.mpr (hfin.subset hsmall)) hsp.2
  · have hsmall : range (splitPick A) ∩ A n ⊆ range (splitPick A) \ splitBranch A (n + 1) := by
      rintro x ⟨hxi, hxA⟩
      exact ⟨hxi, fun hxB => (disjoint_left.mp hdisj) hxB hxA⟩
    exact (not_infinite.mpr (hfin.subset hsmall)) hsp.1

/-- Every countable family of sets of naturals leaves some infinite set
unsplit. -/
theorem exists_unsplit_of_countable (S : Set (Set ℕ)) (hS : S.Countable) :
    ∃ i : Set ℕ, i.Infinite ∧ ∀ s ∈ S, ¬ R0.Splits s i := by
  letI : Nonempty (Set ℕ) := ⟨∅⟩
  rcases Set.countable_iff_exists_subset_range.mp hS with ⟨f, hf⟩
  obtain ⟨i, hi, hn⟩ := exists_unsplit_of_sequence f
  refine ⟨i, hi, ?_⟩
  intro s hs
  rcases hf hs with ⟨n, rfl⟩
  exact hn n

/-- No splitting family is countable. -/
theorem Splitting_not_countable {S : Set (Set ℕ)} (hS : R0.Splitting S) :
    ¬ S.Countable := by
  intro hc
  obtain ⟨i, hi, hn⟩ := exists_unsplit_of_countable S hc
  obtain ⟨s, hs, hsp⟩ := hS i hi
  exact hn s hs hsp

/-- The splitting number is uncountable. -/
theorem aleph0_lt_splittingNumber : Cardinal.aleph0 < R0.splittingNumber := by
  obtain ⟨S, hS, hcard⟩ := R0.exists_minimal_splitting
  by_contra hnot
  have hle : R0.splittingNumber ≤ Cardinal.aleph0 := le_of_not_gt hnot
  have hleS : #S ≤ Cardinal.aleph0 := by
    simpa [hcard] using hle
  exact Splitting_not_countable hS (Cardinal.mk_le_aleph0_iff.mp hleS)

end InfinitaryCombinatorics

import Formalizations.R0.Triangle

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

/-- The precise first-differing-bit threshold stated in Appendix A. -/
theorem triangleValue_ne_of_bit {s t : Set ℕ} {j n : ℕ}
    (hj : ¬ (j ∈ s ↔ j ∈ t)) (hn : 2 ^ (j + 1) - 1 ≤ n) :
    triangleValue s n ≠ triangleValue t n := by
  intro heq
  have hp := Nat.two_pow_pos (j + 1)
  have hl : j + 1 ≤ Nat.log 2 (n + 1) :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  exact hj (prefixValue_agree heq (by omega))

def singletonBlocks : FinSequence ℕ where
  block n := {n}
  finite n := finite_singleton n
  nonempty n := singleton_nonempty n
  disjoint n m hnm := by simpa using hnm

lemma singleton_trace (a : Set ℕ) : trace singletonBlocks a = a := by
  ext n
  simp [trace, singletonBlocks]

/-- Singleton blocks cannot supply the fixed trace-splitting assignment. -/
theorem singleton_blocks_obstruction {M : Set (Set ℕ)} (hM : ADFamily M)
    (S : Set ℕ → Set ℕ) : ¬ TraceSplitCondition M singletonBlocks S := by
  apply no_trace_splitting_of_pairwise_finite singletonBlocks S
  intro a ha b hb hab
  simpa only [singleton_trace] using hM.2 a ha b hb hab

end InfinitaryCombinatorics.Formalizations.R0

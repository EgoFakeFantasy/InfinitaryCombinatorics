import Formalizations.R0.UniformMAD
import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.EquivFin

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

/-- The usual big-endian value of a finite binary word. -/
def wordVector {n : ℕ} (w : Fin n → Bool) : BitVec n :=
  (BitVec.ofBoolListBE (List.ofFn w)).cast (List.length_ofFn)

def wordValue {n : ℕ} (w : Fin n → Bool) : ℕ := (wordVector w).toNat

lemma wordValue_lt {n : ℕ} (w : Fin n → Bool) : wordValue w < 2 ^ n :=
  BitVec.isLt _

lemma wordValue_injective (n : ℕ) : Function.Injective (@wordValue n) := by
  intro w v h
  have hv : wordVector w = wordVector v := BitVec.toNat_inj.mp h
  funext i
  have hh := congrArg (fun b : BitVec n => b.getMsbD i.val) hv
  simpa [wordVector, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt] using hh

def wordFin {n : ℕ} (w : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨wordValue w, wordValue_lt w⟩

lemma wordFin_bijective (n : ℕ) : Function.Bijective (@wordFin n) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro w v h
  exact wordValue_injective n (congrArg Fin.val h)

abbrev BinaryWord := (n : ℕ) × (Fin n → Bool)

def binaryWordCode (w : BinaryWord) : ℕ := 2 ^ w.1 - 1 + wordValue w.2

lemma binaryWordCode_interval (w : BinaryWord) :
    2 ^ w.1 - 1 ≤ binaryWordCode w ∧ binaryWordCode w < 2 ^ (w.1 + 1) - 1 := by
  have hp := Nat.two_pow_pos w.1
  have hv := wordValue_lt w.2
  dsimp [binaryWordCode]
  rw [Nat.pow_succ]
  omega

lemma binaryWordCode_injective : Function.Injective binaryWordCode := by
  rintro ⟨n, w⟩ ⟨m, v⟩ h
  have hn := binaryWordCode_interval ⟨n, w⟩
  have hm := binaryWordCode_interval ⟨m, v⟩
  dsimp only at hn hm
  have heq : n = m := by
    rcases lt_trichotomy n m with hnm | heq | hmn
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hnm
      change 2 ^ (n + 1) ≤ 2 ^ m at hp
      omega
    · exact heq
    · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hmn
      change 2 ^ (m + 1) ≤ 2 ^ n at hp
      omega
  subst m
  have hw : w = v := wordValue_injective n (Nat.add_left_cancel h)
  subst v
  rfl

lemma binaryWordCode_surjective : Function.Surjective binaryWordCode := by
  intro k
  let n := Nat.log 2 (k + 1)
  have hlo : 2 ^ n ≤ k + 1 := Nat.pow_log_le_self 2 (by omega)
  have hhi : k + 1 < 2 ^ (n + 1) := Nat.lt_pow_succ_log_self (by decide) (k + 1)
  have hp := Nat.two_pow_pos n
  have hm : k + 1 - 2 ^ n < 2 ^ n := by rw [Nat.pow_succ] at hhi; omega
  obtain ⟨w, hw⟩ := (wordFin_bijective n).2 ⟨k + 1 - 2 ^ n, hm⟩
  refine ⟨⟨n, w⟩, ?_⟩
  have hv := congrArg Fin.val hw
  change wordValue w = k + 1 - 2 ^ n at hv
  dsimp [binaryWordCode]
  omega

/-- Paper Remark 3.2: the stated interval enumeration is a bijection. -/
noncomputable def binaryWordEquivNat : BinaryWord ≃ ℕ :=
  Equiv.ofBijective binaryWordCode ⟨binaryWordCode_injective, binaryWordCode_surjective⟩

noncomputable def prefixBits (s : Set ℕ) (n : ℕ) : Fin n → Bool := by
  classical
  exact fun i => decide (i.val ∈ s)

noncomputable def prefixValue (s : Set ℕ) (n : ℕ) := wordValue (prefixBits s n)

lemma prefixValue_lt (s : Set ℕ) (n : ℕ) : prefixValue s n < 2 ^ n := wordValue_lt _

lemma prefixValue_agree {s t : Set ℕ} {n j : ℕ} (h : prefixValue s n = prefixValue t n)
    (hj : j < n) : j ∈ s ↔ j ∈ t := by
  have hw := wordValue_injective n h
  have hb := congrFun hw ⟨j, hj⟩
  simpa [prefixBits] using hb

lemma prefixValue_eventually_ne {s t : Set ℕ} (hst : s ≠ t) :
    ∃ N, ∀ n, N ≤ n → prefixValue s n ≠ prefixValue t n := by
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ s ↔ j ∈ t) := by
    by_contra h
    push Not at h
    exact hst (Set.ext h)
  exact ⟨j + 1, fun n hn heq => hj (prefixValue_agree heq (by omega))⟩

end InfinitaryCombinatorics.Formalizations.R0

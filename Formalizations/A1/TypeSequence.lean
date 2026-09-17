import InfinitaryCombinatorics.OrdinalFramework
import Formalizations.A1.CantorPairing
import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
# The fixed depth-one type sequence `t_k` (A1 §3, equation (3.2))

With `π` the Cantor pairing of `CantorPairing.lean` and `(a_k, b_k) = π⁻¹(k)`,
the manuscript puts

    n_k = k + 3,   j_k = a_k + 1,   t_k = 0^{j_k+1} 1 0^{n_k-j_k-1} 1^{n_k-1}.

Read as a `DisjointType (k+3)` from `InfinitaryCombinatorics/DisjointType.lean`,
the left (zero) positions and right (one) positions are

    left  i = i          if i ≤ j_k,   else i + 1,
    right 0 = j_k + 1,   right j = n_k + j   for j ≥ 1.

We prove `width = k+3`, `depth = 1`, and the order consequence (3.3):

    a(j_k) < b(0) < a(j_k+1)   and   max(a) < b(1)

for any realization of `t_k`.
-/

namespace InfinitaryCombinatorics.Formalizations.A1

open InfinitaryCombinatorics

noncomputable section

/-- `a_k ≤ k`: the first coordinate never exceeds the code. -/
theorem cantorFst_le (k : ℕ) : cantorFst k ≤ k := by
  have h := le_cantorPair_left (cantorFst k) (cantorSnd k)
  rw [cantorPair_unpair] at h
  exact h

/-- The gap index `j_k` of equation (3.2). -/
abbrev jk (k : ℕ) : ℕ := cantorFst k + 1

/-- The width `n_k` of equation (3.2). -/
abbrev nk (k : ℕ) : ℕ := k + 3

theorem jk_pos (k : ℕ) : 0 < jk k := by dsimp [jk]; omega
theorem jk_le (k : ℕ) : jk k ≤ k + 1 := by dsimp [jk]; have := cantorFst_le k; omega
theorem jk_lt_nk (k : ℕ) : jk k < nk k := by change jk k < k + 3; have := jk_le k; omega
theorem jk_succ_lt_nk (k : ℕ) : jk k + 1 < nk k := by
  change jk k + 1 < k + 3; have := jk_le k; omega

/-- Position of the `i`-th left (zero) point. -/
def leftPos (k i : ℕ) : ℕ := if i ≤ jk k then i else i + 1

/-- Position of the `j`-th right (one) point. -/
def rightPos (k j : ℕ) : ℕ := if j = 0 then jk k + 1 else nk k + j

theorem leftPos_lt (k : ℕ) {i : ℕ} (hi : i < nk k) : leftPos k i < 2 * nk k := by
  have hnk : nk k = k + 3 := rfl
  have hi' : i < k + 3 := hi
  have hjk := jk_le k
  dsimp [leftPos]
  split_ifs <;> omega

theorem leftPos_strictMono (k : ℕ) {i j : ℕ} (hij : i < j) :
    leftPos k i < leftPos k j := by
  dsimp [leftPos]
  split_ifs <;> omega

theorem rightPos_lt (k : ℕ) {j : ℕ} (hj : j < nk k) : rightPos k j < 2 * nk k := by
  have hnk : nk k = k + 3 := rfl
  have hj' : j < k + 3 := hj
  have hjk := jk_le k
  dsimp [rightPos]
  split_ifs <;> omega

theorem rightPos_strictMono (k : ℕ) {i j : ℕ} (hij : i < j) :
    rightPos k i < rightPos k j := by
  have hnk : nk k = k + 3 := rfl
  have hjk := jk_le k
  dsimp [rightPos]
  split_ifs <;> omega

/-- Left and right positions never collide. -/
theorem leftPos_ne_rightPos (k : ℕ) {i j : ℕ} (hi : i < nk k) (hj : j < nk k) :
    leftPos k i ≠ rightPos k j := by
  have hnk : nk k = k + 3 := rfl
  have hi' : i < k + 3 := hi
  have hj' : j < k + 3 := hj
  have hjk := jk_le k
  by_cases hle : i ≤ jk k
  · by_cases hzero : j = 0
    · dsimp [leftPos, rightPos]
      simp [hle, hzero]
      omega
    · have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
      dsimp [leftPos, rightPos]
      simp [hle, hzero]
      omega
  · by_cases hzero : j = 0
    · dsimp [leftPos, rightPos]
      simp [hle, hzero]
      omega
    · have hjpos : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hzero)
      dsimp [leftPos, rightPos]
      simp [hle, hzero]
      omega

/-- Every position is occupied. -/
theorem exists_pos (k : ℕ) {p : ℕ} (hp : p < 2 * nk k) :
    (∃ i : ℕ, i < nk k ∧ leftPos k i = p) ∨
    (∃ j : ℕ, j < nk k ∧ rightPos k j = p) := by
  have hnk : nk k = k + 3 := rfl
  have hp' : p < 2 * (k + 3) := hp
  have hjk := jk_le k
  by_cases hp1 : p ≤ jk k
  · left
    refine ⟨p, ?_, ?_⟩
    · omega
    · dsimp [leftPos]; simp [hp1]
  · have hp1' : jk k < p := lt_of_not_ge hp1
    by_cases hp2 : p = jk k + 1
    · right
      refine ⟨0, ?_, ?_⟩
      · omega
      · dsimp [rightPos]; simp [hp2]
    · have hp2' : jk k + 1 < p := by omega
      by_cases hp3 : p ≤ k + 3
      · left
        refine ⟨p - 1, ?_, ?_⟩
        · omega
        · dsimp [leftPos]
          have hgt : ¬ p - 1 ≤ jk k := by omega
          simp [hgt]
          omega
      · right
        have hp3' : k + 3 < p := lt_of_not_ge hp3
        refine ⟨p - (k + 3), ?_, ?_⟩
        · omega
        · dsimp [rightPos]
          have hne : p - (k + 3) ≠ 0 := by omega
          simp [hne]
          omega

/-- The fixed type `t_k` of equation (3.2). -/
noncomputable def typeSeq (k : ℕ) : DisjointType (nk k) where
  left :=
    OrderEmbedding.ofStrictMono
      (fun i : Fin (nk k) =>
        (⟨leftPos k i.val, leftPos_lt k i.isLt⟩ : Fin (2 * nk k)))
      (fun i j hij => by
        change leftPos k i.val < leftPos k j.val
        exact leftPos_strictMono k hij)
  right :=
    OrderEmbedding.ofStrictMono
      (fun j : Fin (nk k) =>
        (⟨rightPos k j.val, rightPos_lt k j.isLt⟩ : Fin (2 * nk k)))
      (fun i j hij => by
        change rightPos k i.val < rightPos k j.val
        exact rightPos_strictMono k hij)
  disjoint := by
    intro i j h
    exact leftPos_ne_rightPos k i.isLt j.isLt (Fin.ext_iff.mp h)
  cover := by
    intro p
    rcases exists_pos k p.isLt with ⟨i, hi, hpi⟩ | ⟨j, hj, hpj⟩
    · left
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Fin.ext
      simpa using hpi
    · right
      refine ⟨⟨j, hj⟩, ?_⟩
      apply Fin.ext
      simpa using hpj

theorem typeSeq_left_apply (k : ℕ) (i : Fin (nk k)) :
    ((typeSeq k).left i).val = leftPos k i.val := rfl

theorem typeSeq_right_apply (k : ℕ) (j : Fin (nk k)) :
    ((typeSeq k).right j).val = rightPos k j.val := rfl

/-- `t_k` has depth at most one: `b(1)` dominates every left point. -/
theorem typeSeq_depthLE_one (k : ℕ) :
    (typeSeq k).DepthLE (⟨1, by change 1 < k + 3; omega⟩ : Fin (nk k)) := by
  left
  intro i
  change leftPos k i.val < rightPos k 1
  have hnk : nk k = k + 3 := rfl
  have hi' : i.val < k + 3 := i.isLt
  have hjk := jk_le k
  dsimp [leftPos, rightPos]
  split_ifs <;> omega

/-- `t_k` does not have depth zero, in either of the two possible directions. -/
theorem typeSeq_not_depthLE_zero (k : ℕ) :
    ¬ (typeSeq k).DepthLE (⟨0, by change 0 < k + 3; omega⟩ : Fin (nk k)) := by
  rintro (h | h)
  · have hlt := jk_succ_lt_nk k
    specialize h ⟨jk k + 1, hlt⟩
    change leftPos k (jk k + 1) < rightPos k 0 at h
    have hgt : ¬ jk k + 1 ≤ jk k := by omega
    simp [leftPos, rightPos, hgt] at h
  · specialize h ⟨0, by change 0 < k + 3; omega⟩
    change rightPos k 0 < leftPos k 0 at h
    have h0le : 0 ≤ jk k := Nat.zero_le _
    simp [leftPos, rightPos, h0le] at h

theorem typeSeq_depth (k : ℕ) : (typeSeq k).depth = 1 := by
  have hle : (typeSeq k).depth ≤ 1 :=
    (typeSeq k).depth_le ⟨1, by change 1 < k + 3; omega⟩ (typeSeq_depthLE_one k)
  have hne : (typeSeq k).depth ≠ 0 := by
    intro h0
    have hs := (typeSeq k).depth_spec
    have hz : (typeSeq k).DepthLE (⟨0, by change 0 < k + 3; omega⟩ : Fin (nk k)) := by
      simpa [h0] using hs.choose_spec
    exact typeSeq_not_depthLE_zero k hz
  omega

/-- The order facts (3.3), for an arbitrary realization of `t_k`. -/
theorem typeSeq_order (k : ℕ) {α : Type*} [LinearOrder α] {a b : Fin (nk k) → α}
    (h : (typeSeq k).Realizes a b) :
    a ⟨jk k, jk_lt_nk k⟩ < b ⟨0, by change 0 < k + 3; omega⟩ ∧
    b ⟨0, by change 0 < k + 3; omega⟩ < a ⟨jk k + 1, jk_succ_lt_nk k⟩ ∧
    ∀ i : Fin (nk k), a i < b ⟨1, by change 1 < k + 3; omega⟩ := by
  obtain ⟨e, ha, hb⟩ := h
  have lt_ab (i j : Fin (nk k)) :
      a i < b j ↔ (typeSeq k).left i < (typeSeq k).right j := by
    rw [← ha i, ← hb j]
    exact e.lt_iff_lt
  have lt_ba (j i : Fin (nk k)) :
      b j < a i ↔ (typeSeq k).right j < (typeSeq k).left i := by
    rw [← hb j, ← ha i]
    exact e.lt_iff_lt
  refine ⟨?_, ?_, ?_⟩
  · apply (lt_ab ⟨jk k, jk_lt_nk k⟩ ⟨0, by change 0 < k + 3; omega⟩).mpr
    change leftPos k (jk k) < rightPos k 0
    simp [leftPos, rightPos]
  · apply (lt_ba ⟨0, by change 0 < k + 3; omega⟩ ⟨jk k + 1, jk_succ_lt_nk k⟩).mpr
    change rightPos k 0 < leftPos k (jk k + 1)
    have hgt : ¬ jk k + 1 ≤ jk k := by omega
    simp [leftPos, rightPos, hgt]
  · intro i
    apply (lt_ab i ⟨1, by change 1 < k + 3; omega⟩).mpr
    change leftPos k i.val < rightPos k 1
    have hnk : nk k = k + 3 := rfl
    have hi' : i.val < k + 3 := i.isLt
    have hjk := jk_le k
    dsimp [leftPos, rightPos]
    split_ifs <;> omega

/-- The width function of the sequence: `width k + 1 = n_k = k + 3`. -/
def widthSeq (k : ℕ) : ℕ := k + 2

/-- `t_k` packaged at the type `DisjointType (widthSeq k + 1)` used by `TypeGuessing`. -/
noncomputable def typeSeqW (k : ℕ) : DisjointType (widthSeq k + 1) := by
  dsimp [widthSeq]
  exact typeSeq k

theorem typeSeqW_depth (k : ℕ) : (typeSeqW k).depth = 1 := by
  dsimp [typeSeqW]
  exact typeSeq_depth k

/-- The sequence `t⃗` has uniformly bounded depth, hence falls under BDTG. -/
theorem typeSeqW_boundedDepth : BoundedTypeDepth widthSeq typeSeqW := by
  refine ⟨1, ?_⟩
  intro k
  rw [typeSeqW_depth]

end

end InfinitaryCombinatorics.Formalizations.A1

import Mathlib.Order.Basic
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Cantor pairing on `ℕ` (A1 §3, equation (3.1))

The manuscript uses the Cantor pairing function

    π(a, b) = (a + b)(a + b + 1) / 2 + b.

The closed form is proved below. The inverse uses the fact that values of π split
`ℕ` into consecutive blocks `B_s = [tri s, tri (s+1))` of length `s + 1`,
where `tri 0 = 0` and `tri (s+1) = tri s + s + 1`. Inside block `s` the value
encodes the pair `(s - b, b)` with `b = value - tri s`.

The coordinate maps are proved inverse to `cantorPair` in both directions.
The inverse is specified by least-number search; bijectivity is proved locally.
-/

namespace InfinitaryCombinatorics.Formalizations.A1

/-- Triangular numbers, defined by recursion so that the successor step is `rfl`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | n + 1 => tri n + n + 1

@[simp] theorem tri_zero : tri 0 = 0 := rfl
@[simp] theorem tri_succ (n : ℕ) : tri (n + 1) = tri n + n + 1 := rfl

theorem tri_lt_succ (n : ℕ) : tri n < tri (n + 1) := by
  change tri n < tri n + n + 1
  omega

theorem tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  induction b with
  | zero =>
      have : a = 0 := Nat.eq_zero_of_le_zero h
      subst a
      rfl
  | succ b ih =>
      rcases lt_or_eq_of_le h with hlt | heq
      · have ih' : tri a ≤ tri b := ih (Nat.le_of_lt_succ hlt)
        calc
          tri a ≤ tri b := ih'
          _ ≤ tri (b + 1) := by
            change tri b ≤ tri b + b + 1
            omega
      · subst a
        rfl

theorem self_le_tri (n : ℕ) : n ≤ tri n := by
  induction n with
  | zero => simp [tri]
  | succ n ih =>
      change n + 1 ≤ tri n + n + 1
      omega

/-- Every `n` lies in some block `[tri s, tri (s+1))`. -/
theorem exists_block (n : ℕ) : ∃ s : ℕ, n < tri (s + 1) := by
  refine ⟨n, ?_⟩
  have h := self_le_tri (n + 1)
  omega

/-- The block index of `n`: the least `s` with `n < tri (s+1)`. -/
noncomputable def block (n : ℕ) : ℕ := Nat.find (exists_block n)

theorem block_spec (n : ℕ) : n < tri (block n + 1) :=
  Nat.find_spec (exists_block n)

theorem block_min (n : ℕ) {s : ℕ} (h : n < tri (s + 1)) : block n ≤ s :=
  Nat.find_min' (exists_block n) h

theorem tri_le_block (n : ℕ) : tri (block n) ≤ n := by
  cases hs : block n with
  | zero => simp [tri]
  | succ s =>
      by_contra h
      have hnot : ¬ tri (block n) ≤ n := by simpa [hs] using h
      have hlt : n < tri (s + 1) := by
        have : n < tri (block n) := lt_of_not_ge hnot
        simpa [hs] using this
      have : block n ≤ s := block_min n hlt
      omega

/-- The offset inside the block; this is the second coordinate. -/
noncomputable def offset (n : ℕ) : ℕ := n - tri (block n)

theorem offset_le_block (n : ℕ) : offset n ≤ block n := by
  dsimp [offset]
  have hs := block_spec n
  have hs' : n < tri (block n) + block n + 1 := by
    simpa [tri_succ] using hs
  omega

/-- The Cantor pairing function of equation (3.1), in block form. -/
def cantorPair (a b : ℕ) : ℕ := tri (a + b) + b

/-- First coordinate of the inverse. -/
noncomputable def cantorFst (n : ℕ) : ℕ := block n - offset n

/-- Second coordinate of the inverse. -/
noncomputable def cantorSnd (n : ℕ) : ℕ := offset n

theorem block_pair (a b : ℕ) : block (cantorPair a b) = a + b := by
  apply le_antisymm
  · apply block_min
    dsimp [cantorPair]
    calc
      tri (a + b) + b < tri (a + b) + (a + b) + 1 := by omega
      _ = tri ((a + b) + 1) := (tri_succ (a + b)).symm
  · by_contra h
    have hlt : block (cantorPair a b) < a + b := lt_of_not_ge h
    have hsle : block (cantorPair a b) + 1 ≤ a + b := Nat.succ_le_of_lt hlt
    have hmono : tri (block (cantorPair a b) + 1) ≤ tri (a + b) := tri_mono hsle
    have hs := block_spec (cantorPair a b)
    have hcontra : cantorPair a b < tri (a + b) := lt_of_lt_of_le hs hmono
    dsimp [cantorPair] at hcontra
    omega

theorem cantorSnd_pair (a b : ℕ) : cantorSnd (cantorPair a b) = b := by
  dsimp [cantorSnd, offset]
  rw [block_pair]
  dsimp [cantorPair]
  omega

theorem cantorFst_pair (a b : ℕ) : cantorFst (cantorPair a b) = a := by
  dsimp [cantorFst, offset]
  rw [block_pair]
  dsimp [cantorPair]
  omega

theorem cantorPair_unpair (n : ℕ) : cantorPair (cantorFst n) (cantorSnd n) = n := by
  dsimp [cantorPair, cantorFst, cantorSnd, offset]
  have htri : tri (block n) ≤ n := tri_le_block n
  have hb : n - tri (block n) ≤ block n := offset_le_block n
  have hsum : block n - (n - tri (block n)) + (n - tri (block n)) = block n := by omega
  rw [hsum]
  omega

/-- Equation (3.1) also satisfies `π(a,b) ≥ a`; used for `a_k ≤ k` in Lemma 3.1. -/
theorem le_cantorPair_left (a b : ℕ) : a ≤ cantorPair a b := by
  dsimp [cantorPair]
  have h := self_le_tri (a + b)
  omega

theorem cantorPair_inj {a b c d : ℕ} (h : cantorPair a b = cantorPair c d) :
    a = c ∧ b = d := by
  have hb : b = d := by
    calc
      b = cantorSnd (cantorPair a b) := (cantorSnd_pair a b).symm
      _ = cantorSnd (cantorPair c d) := by rw [h]
      _ = d := cantorSnd_pair c d
  have ha : a = c := by
    calc
      a = cantorFst (cantorPair a b) := (cantorFst_pair a b).symm
      _ = cantorFst (cantorPair c d) := by rw [h]
      _ = c := cantorFst_pair c d
  exact ⟨ha, hb⟩

theorem cantorPair_injective : Function.Injective (fun p : ℕ × ℕ => cantorPair p.1 p.2) := by
  intro x y h
  obtain ⟨h1, h2⟩ := cantorPair_inj h
  cases x with
  | mk xa xb =>
    cases y with
    | mk ya yb =>
      simp at h1 h2
      simp [h1, h2]

/-- The manuscript's `(a_k, b_k)`: the unique inverse image of `k`. -/
noncomputable def pairInv (k : ℕ) : ℕ × ℕ := (cantorFst k, cantorSnd k)

theorem pairInv_spec (k : ℕ) : cantorPair (pairInv k).1 (pairInv k).2 = k := by
  dsimp [pairInv]
  exact cantorPair_unpair k

theorem pairInv_unique (k a b : ℕ) (h : cantorPair a b = k) :
    (pairInv k).1 = a ∧ (pairInv k).2 = b := by
  obtain ⟨h1, h2⟩ := cantorPair_inj (h.trans (pairInv_spec k).symm)
  exact ⟨h1.symm, h2.symm⟩

/-- The recursive triangular numbers agree with the manuscript's arithmetic formula. -/
theorem two_mul_tri (n : ℕ) : 2 * tri n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tri_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
    omega

theorem tri_closedForm (n : ℕ) : tri n = n * (n + 1) / 2 := by
  have := two_mul_tri n
  omega

/-- Exact equality with equation (3.1), not a change of pairing convention. -/
theorem cantorPair_closedForm (a b : ℕ) :
    cantorPair a b = (a + b) * (a + b + 1) / 2 + b := by
  rw [cantorPair, tri_closedForm]
end InfinitaryCombinatorics.Formalizations.A1

import InfinitaryCombinatorics.Delta
import Mathlib.Tactic.Push

/-! Finite-prefix fusion on the full binary space. -/
namespace InfinitaryCombinatorics.Formalizations.A2

abbrev BinarySeq := ℕ → Bool

def Agree (n : ℕ) (x y : BinarySeq) : Prop := ∀ k < n, x k = y k

theorem agree_refl (n : ℕ) (x : BinarySeq) : Agree n x x := fun _ _ => rfl

theorem agree_symm {n : ℕ} {x y : BinarySeq} (h : Agree n x y) : Agree n y x :=
  fun k hk => (h k hk).symm

theorem agree_trans {n : ℕ} {x y z : BinarySeq}
    (h : Agree n x y) (h' : Agree n y z) : Agree n x z :=
  fun k hk => (h k hk).trans (h' k hk)

theorem agree_mono {m n : ℕ} (hmn : m ≤ n) {x y : BinarySeq}
    (h : Agree n x y) : Agree m x y := fun k hk => h k (hk.trans_le hmn)

theorem agree_update (n : ℕ) (s : BinarySeq) (b : Bool) :
    Agree n (Function.update s n b) s := by
  intro k hk
  simp [Function.update, ne_of_lt hk]

theorem agree_succ_update (n : ℕ) (s x : BinarySeq) (b : Bool) :
    Agree (n + 1) x (Function.update s n b) ↔ Agree n x s ∧ x n = b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro k hk
      simpa [Function.update, ne_of_lt hk] using h k (by omega)
    · simpa using h n (by omega)
  · rintro ⟨h, hb⟩ k hk
    by_cases hkn : k = n
    · subst k; simpa using hb
    · simpa [Function.update, hkn] using h k (by omega)

/-- Compatible finite prefixes selected with dependent choice have a common branch.
The offset permits starting from a prescribed first bit. -/
theorem binary_fusion (offset : ℕ) (P : ℕ → BinarySeq → Prop)
    (s₀ : BinarySeq) (h₀ : P 0 s₀)
    (step : ∀ n s, P n s → ∃ t, P (n + 1) t ∧ Agree (n + offset) t s) :
    ∃ z : BinarySeq, ∀ n, ∃ s, P n s ∧ Agree (n + offset) z s := by
  classical
  let states : (n : ℕ) → {s : BinarySeq // P n s} :=
    fun n => Nat.rec ⟨s₀, h₀⟩
      (fun n s => ⟨(step n s.val s.property).choose,
        (step n s.val s.property).choose_spec.1⟩) n
  have hs (n : ℕ) : Agree (n + offset) (states (n + 1)).val (states n).val :=
    (step n (states n).val (states n).property).choose_spec.2
  have compat (n m : ℕ) (hnm : n ≤ m) :
      Agree (n + offset) (states m).val (states n).val := by
    induction m, hnm using Nat.le_induction with
    | base => exact agree_refl _ _
    | succ m hnm ih =>
      exact agree_trans (agree_mono (by omega) (hs m)) ih
  let z : BinarySeq := fun k => (states (k + 1)).val k
  refine ⟨z, fun n => ⟨(states n).val, (states n).property, ?_⟩⟩
  intro k hk
  by_cases hn : n ≤ k + 1
  · exact compat n (k + 1) hn k hk
  · exact (compat (k + 1) n (by omega) k (by omega)).symm

/-- Lambie-Hanson--Soukup's maximality lemma at length omega, with its
full diagonal proof (no maximality premise is assumed). -/
theorem delta_maximal (d : BinarySeq → ℕ) :
    ∃ x y : BinarySeq, ∃ hxy : x ≠ y, d x = delta x y hxy ∧ d y = delta x y hxy := by
  classical
  by_contra hn
  let P : ℕ → BinarySeq → Prop := fun n s =>
    ∀ x, Agree n x s → ∀ k < n, d x ≠ k
  have step (n : ℕ) (s : BinarySeq) (hs : P n s) :
      ∃ t, P (n + 1) t ∧ Agree n t s := by
    have child : ∃ b : Bool, ∀ x,
        Agree (n + 1) x (Function.update s n b) → d x ≠ n := by
      by_contra h
      push Not at h
      obtain ⟨x, hx, hdx⟩ := h false
      obtain ⟨y, hy, hdy⟩ := h true
      obtain ⟨hx', hxb⟩ := (agree_succ_update n s x false).mp hx
      obtain ⟨hy', hyb⟩ := (agree_succ_update n s y true).mp hy
      have hd : FirstDifference x y n :=
        ⟨by simp [hxb, hyb], fun k hk => (hx' k hk).trans (hy' k hk).symm⟩
      have he : delta x y hd.ne = n := (delta_spec x y hd.ne).unique hd
      exact hn ⟨x, y, hd.ne, hdx.trans he.symm, hdy.trans he.symm⟩
    obtain ⟨b, hb⟩ := child
    refine ⟨Function.update s n b, ?_, agree_update n s b⟩
    intro x hx k hk
    by_cases hkn : k < n
    · exact hs x ((agree_succ_update n s x b).mp hx).1 k hkn
    · have : k = n := by omega
      subst k
      exact hb x hx
  obtain ⟨z, hz⟩ := binary_fusion 0 P (fun _ => false)
    (by intro x hx k hk; omega) (by simpa using step)
  obtain ⟨s, hs, hzs⟩ := hz (d z + 1)
  exact hs z hzs (d z) (by omega) rfl

end InfinitaryCombinatorics.Formalizations.A2

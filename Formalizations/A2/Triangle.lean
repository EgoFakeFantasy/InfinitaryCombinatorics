import Formalizations.A2.Coordinates
import Formalizations.A2.Cliques
import Formalizations.A2.Statements

/-! Rigidity and the triangle theorem at length omega. -/
namespace InfinitaryCombinatorics.Formalizations.A2
universe u

def NatRegressive (c : PairColoring BinarySeq ℕ) : Prop :=
  ∀ x y (hxy : x ≠ y), 0 < delta x y hxy → c.color x y < delta x y hxy

theorem rigid_lower_bound (c : PairColoring BinarySeq ℕ) (hc : NatRegressive c)
    (hno : ¬ c.HasClique 3) (n : ℕ) :
    ∀ x y : BinarySeq, x 0 = false → y 0 = false → ∀ hxy : x ≠ y,
      n + 1 ≤ delta x y hxy → n ≤ c.color x y := by
  classical
  induction n with
  | zero => intro x y hx hy hxy hd; exact Nat.zero_le _
  | succ n ih =>
    intro x y hx hy hxy hd
    have hl := ih x y hx hy hxy (by omega)
    by_contra hbad
    have hcol : c.color x y = n := by omega
    let z : BinarySeq := Function.update x (n + 1) (!(x (n + 1)))
    have hz : z 0 = false := by simp [z, hx]
    have hxn : x (n + 1) = y (n + 1) := (delta_spec x y hxy).2 _ (by omega)
    have hdx : FirstDifference x z (n + 1) := by
      refine ⟨by simp [z], ?_⟩
      intro k hk
      change x k = Function.update x (n + 1) (!(x (n + 1))) k
      simp [Function.update, ne_of_lt hk]
    have hdy : FirstDifference y z (n + 1) := by
      refine ⟨by simp [z, ← hxn], ?_⟩
      intro k hk
      have he := (delta_spec x y hxy).2 k (by omega)
      simpa [z, Function.update, ne_of_lt hk] using he.symm
    have ex := (delta_spec x z hdx.ne).unique hdx
    have ey := (delta_spec y z hdy.ne).unique hdy
    have cx : c.color x z = n := by
      have lo := ih x z hx hz hdx.ne (by omega)
      have up := hc x z hdx.ne (by omega)
      omega
    have cy : c.color y z = n := by
      have lo := ih y z hy hz hdy.ne (by omega)
      have up := hc y z hdy.ne (by omega)
      omega
    exact hno (clique3_of_edges c hxy hdy.ne hdx.ne hcol cy cx)

/-- Lemma 5.2 in the paper, in the equivalent natural-coordinate presentation. -/
theorem rigid_on_zero_cone (c : PairColoring BinarySeq ℕ) (hc : NatRegressive c)
    (hno : ¬ c.HasClique 3) {x y : BinarySeq} (hx : x 0 = false) (hy : y 0 = false)
    (hxy : x ≠ y) : c.color x y = delta x y hxy - 1 := by
  have hp : 0 < delta x y hxy := by
    by_contra h
    have hz : delta x y hxy = 0 := by omega
    have hn := (delta_spec x y hxy).1
    rw [hz, hx, hy] at hn
    exact hn rfl
  have lo := rigid_lower_bound c hc hno (delta x y hxy - 1) x y hx hy hxy (by omega)
  have up := hc x y hxy hp
  omega

def prependZero (s : BinarySeq) : BinarySeq
  | 0 => false
  | n + 1 => s n

theorem prepend_firstDifference {s t : BinarySeq} {n : ℕ}
    (h : FirstDifference s t n) : FirstDifference (prependZero s) (prependZero t) (n + 1) := by
  refine ⟨h.1, ?_⟩
  intro k hk
  cases k with
  | zero => rfl
  | succ k => exact h.2 k (by omega)

theorem nat_triangle (c : PairColoring BinarySeq ℕ) (hc : NatRegressive c) : c.HasClique 3 := by
  classical
  by_contra hno
  let z : BinarySeq := fun _ => true
  obtain ⟨s, t, hst, hs, ht⟩ := delta_maximal (fun u => c.color (prependZero u) z)
  have hd := prepend_firstDifference (delta_spec s t hst)
  have he := (delta_spec (prependZero s) (prependZero t) hd.ne).unique hd
  have hxz : prependZero s ≠ z := by intro h; have := congrFun h 0; contradiction
  have hyz : prependZero t ≠ z := by intro h; have := congrFun h 0; contradiction
  have hcxy : c.color (prependZero s) (prependZero t) = delta s t hst := by
    have h := rigid_on_zero_cone c hc hno (x := prependZero s) (y := prependZero t) rfl rfl hd.ne
    simpa [he] using h
  exact hno (clique3_of_edges c hd.ne hyz hxz hcxy ht hs)

/-- Theorem 2.4, transported back to the original ordinal branch and colour types. -/
theorem theorem_2_4 : Theorem24.{u} := by
  classical
  intro c hc
  let cN : PairColoring BinarySeq ℕ :=
    (c.pullback omegaBranch.{u}).recolor finiteIndex
  have hN : NatRegressive cN := by
    intro s t hst hp
    have hd := omegaBranch_firstDifference (delta_spec s t hst)
    have he := (delta_spec (omegaBranch s) (omegaBranch t) hd.ne).unique hd
    have hpos : (0 : Ordinal.{u}) < (delta (omegaBranch s) (omegaBranch t) hd.ne).val := by
      rw [he]
      change (0 : Ordinal.{u}) < (delta s t hst : ℕ)
      exact_mod_cast hp
    have up := hc (omegaBranch s) (omegaBranch t) hd.ne hpos
    rw [he] at up
    rw [finiteIndex_spec (c.color (omegaBranch s) (omegaBranch t))] at up
    change (finiteIndex (c.color (omegaBranch s) (omegaBranch t)) : Ordinal.{u}) <
      (delta s t hst : ℕ) at up
    exact_mod_cast up
  obtain ⟨e, m, hm⟩ := nat_triangle cN hN
  refine ⟨e.trans ⟨omegaBranch.{u}, omegaBranch_injective⟩, natCoord le_rfl m, ?_⟩
  intro i j hij
  apply Subtype.ext
  change (c.color (omegaBranch (e i)) (omegaBranch (e j))).val = (m : Ordinal.{u})
  rw [finiteIndex_spec]
  exact congrArg (fun n : ℕ => (n : Ordinal.{u})) (hm i j hij)

end InfinitaryCombinatorics.Formalizations.A2

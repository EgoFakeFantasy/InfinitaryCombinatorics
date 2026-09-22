import Formalizations.A2.Coordinates
import Formalizations.A2.Cliques
import Formalizations.A2.Statements

/-! The full cone-chain proof for every ordinal strictly above omega. -/
namespace InfinitaryCombinatorics.Formalizations.A2
open Set
universe u

theorem theorem_2_2 : Theorem22.{u} := by
  classical
  intro κ hκ c hc
  by_contra hn
  let R := natRestrict hκ.le
  let P : ℕ → BinarySeq → Prop := fun n s =>
    s 0 = false ∧ ∀ x y : Branch κ,
      Agree (n + 1) (R x) s → Agree (n + 1) (R y) s → x ≠ y →
        (n : Ordinal.{u}) ≤ (c.color x y).val
  have hstep (n : ℕ) (s : BinarySeq) (hs : P n s) :
      ∃ t, P (n + 1) t ∧ Agree (n + 1) t s := by
    let A : Bool → Set (Branch κ) := fun b =>
      {x | Agree (n + 2) (R x) (Function.update s (n + 1) b)}
    let k : Set.Iio κ := natCoord hκ.le n
    have parent (b : Bool) (x : Branch κ) (hx : x ∈ A b) :
        Agree (n + 1) (R x) s :=
      ((agree_succ_update (n + 1) s (R x) b).mp hx).1
    have side (b : Bool) (x : Branch κ) (hx : x ∈ A b) : R x (n + 1) = b :=
      ((agree_succ_update (n + 1) s (R x) b).mp hx).2
    have inzero (b : Bool) : A b ⊆ zeroCone κ (zero_lt_of_omega_lt hκ) := by
      intro x hx
      change R x 0 = false
      exact (parent b x hx 0 (by omega)).trans hs.1
    have hdisj : Disjoint (A false) (A true) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have := (side false x hx).symm.trans (side true x hy)
      contradiction
    have cross : ∀ x ∈ A false, ∀ y ∈ A true, c.color x y = k := by
      intro x hx y hy
      have hd : FirstDifference (R x) (R y) (n + 1) :=
        ⟨by simp [side false x hx, side true y hy],
          fun j hj => (parent false x hx j hj).trans (parent true y hy j hj).symm⟩
      have hd' := firstDifference_of_nat hκ.le hd
      have he := (delta_spec x y hd'.ne).unique hd'
      have hpos : (0 : Ordinal.{u}) < (delta x y hd'.ne).val := by
        rw [he]
        change (0 : Ordinal.{u}) < (n + 1 : ℕ)
        exact_mod_cast Nat.zero_lt_succ n
      have hu := hc x y hd'.ne hpos
      rw [he] at hu
      have hl := hs.2 x y (parent false x hx) (parent true y hy) hd'.ne
      have hu' : (c.color x y).val ≤ (n : Ordinal.{u}) := by
        apply (Order.lt_succ_iff).mp
        simpa [natCoord, Order.succ_eq_add_one, Nat.cast_add] using hu
      exact Subtype.ext (le_antisymm hu' hl)
    have good : ∃ b : Bool, ∀ x ∈ A b, ∀ y ∈ A b, x ≠ y → c.color x y ≠ k := by
      by_contra h
      push Not at h
      obtain ⟨x, hx, x', hx', hxx, hcolx⟩ := h false
      obtain ⟨y, hy, y', hy', hyy, hcoly⟩ := h true
      obtain ⟨e, he, hc'⟩ := clique4_in c k hdisj (inzero false) (inzero true) cross
        ⟨x, hx, x', hx', hxx, hcolx⟩ ⟨y, hy, y', hy', hyy, hcoly⟩
      exact hn ⟨k, Ordinal.natCast_lt_omega0 n, e, he, hc'⟩
    obtain ⟨b, hb⟩ := good
    refine ⟨Function.update s (n + 1) b, ⟨?_, ?_⟩, agree_update (n + 1) s b⟩
    · simpa [Function.update] using hs.1
    · intro x y hx hy hxy
      have hl := hs.2 x y (parent b x hx) (parent b y hy) hxy
      have hne : (c.color x y).val ≠ (n : Ordinal.{u}) := by
        intro he
        exact hb x hx y hy hxy (Subtype.ext he)
      have hlt := lt_of_le_of_ne hl (Ne.symm hne)
      simpa [Order.succ_eq_add_one, Nat.cast_add] using (Order.succ_le_iff).mpr hlt
  obtain ⟨s, hs⟩ := binary_fusion 1 P (fun _ => false)
    ⟨rfl, fun _ _ _ _ _ => bot_le⟩ hstep
  let x := extendOmega hκ s false
  let y := extendOmega hκ s true
  have hd : FirstDifference x y ⟨Ordinal.omega0, hκ⟩ := extendOmega_firstDifference hκ s
  have he := (delta_spec x y hd.ne).unique hd
  have hpos : (0 : Ordinal.{u}) < (delta x y hd.ne).val := by
    rw [he]
    exact Ordinal.omega0_pos
  have hfin : (c.color x y).val < Ordinal.omega0 := by
    simpa [he] using hc x y hd.ne hpos
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hfin
  obtain ⟨t, ht, hst⟩ := hs (m + 1)
  have hx : Agree (m + 1 + 1) (R x) t := by simpa [Agree, R, x, natRestrict] using hst
  have hy : Agree (m + 1 + 1) (R y) t := by simpa [Agree, R, y, natRestrict] using hst
  have hbad := ht.2 x y hx hy hd.ne
  rw [hm] at hbad
  have : m + 1 ≤ m := by exact_mod_cast hbad
  omega

end InfinitaryCombinatorics.Formalizations.A2

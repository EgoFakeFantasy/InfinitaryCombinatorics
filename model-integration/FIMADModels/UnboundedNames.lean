import FIMADModels.NaturalNames
import YesMetaZFC.Model.Boolean.Maximum

/-! Bounded quantifiers over the actual omega graph and witnesses in unbounded
set names. All quantifiers over names range over the full graph-name universe.
No enumeration or decision relation is supplied as an input. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC.Model.Boolean BV_graph
universe u
variable {P : Type u} (R : Order P)

theorem omega_sup (p : BV_name (Regular R) → Regular R) (hp : Stable (algebra R) p) :
    (algebra R).iSup (fun G => (algebra R).meet
      (bv_mem (algebra R) G (omega (algebra R))) (p G)) =
        (algebra R).iSup (fun n : Nat => p (natural R n)) := by
  rw [bounded_sup (algebra R) _ _ hp]
  apply (algebra R).le_antisymm
  · apply ((algebra R).iSup_le_iff _ _).mpr
    rintro ⟨a, ha⟩
    cases a with
    | none => exact False.elim ha
    | some a =>
      have he : a = List.replicate a.length PUnit.unit :=
        List.ext_getElem (by simp) (fun _ _ _ => Subsingleton.elim _ _)
      change (algebra R).le ((algebra R).meet (algebra R).top
        (p (omega_piece (algebra R) a))) _
      rw [(algebra R).top_meet, he]
      exact (algebra R).le_iSup (fun n : Nat => p (natural R n)) a.length
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro n
    have h := (algebra R).le_iSup
      (fun a : (omega (algebra R)).Child (omega (algebra R)).root =>
        (algebra R).meet ((omega (algebra R)).val a (omega (algebra R)).root)
          (p ((omega (algebra R)).at_node a)))
      ⟨some (List.replicate n PUnit.unit), True.intro⟩
    simpa only [omega, BA_alg.top_meet, natural, omega_piece] using h

theorem omega_all (p : BV_name (Regular R) → Regular R) (hp : Stable (algebra R) p) :
    (algebra R).iInf (fun G => (algebra R).imp
      (bv_mem (algebra R) G (omega (algebra R))) (p G)) =
        (algebra R).iInf (fun n : Nat => p (natural R n)) := by
  apply (algebra R).le_antisymm
  · apply ((algebra R).le_iInf_iff _ _).mpr
    intro n
    have h := (bounded_all (algebra R) (omega (algebra R)) p hp _).mp
      ((algebra R).le_refl _) ⟨some (List.replicate n PUnit.unit), True.intro⟩
    simpa only [omega, BA_alg.meet_top, natural, omega_piece] using h
  · apply (bounded_all (algebra R) (omega (algebra R)) p hp _).mpr
    rintro ⟨a, ha⟩
    cases a with
    | none => exact False.elim ha
    | some a =>
      have he : a = List.replicate a.length PUnit.unit :=
        List.ext_getElem (by simp) (fun _ _ _ => Subsingleton.elim _ _)
      change (algebra R).le ((algebra R).meet _ (algebra R).top)
        (p (omega_piece (algebra R) a))
      rw [(algebra R).meet_top, he]
      exact (algebra R).iInf_le (fun n : Nat => p (natural R n)) a.length

def above (X Y : BV_name (Regular R)) : Regular R :=
  (algebra R).join (bv_mem (algebra R) X Y) (bv_eq (algebra R) X Y)

theorem above_left_stable (Y : BV_name (Regular R)) :
    Stable (algebra R) (fun X => above R X Y) := by
  apply stable_join (algebra R) (stable_elem (algebra R) Y)
  intro G H
  dsimp only
  rw [eq_symm (algebra R) G Y, eq_symm (algebra R) H Y]
  exact stable_eq (algebra R) Y G H

theorem above_right_stable (X : BV_name (Regular R)) :
    Stable (algebra R) (above R X) :=
  stable_join (algebra R) (stable_set (algebra R) X) (stable_eq (algebra R) X)

def tailValue (G : BV_name (Regular R)) (i : Nat) : Regular R :=
  (algebra R).iSup (fun k : {k : Nat // i ≤ k} => bv_mem (algebra R) (natural R k.1) G)

/-- Full bounded-name semantics of forall x in omega, exists y in omega:
x <= y and y belongs to G. This is not an external pointwise assertion. -/
def unboundedValue (G : BV_name (Regular R)) : Regular R :=
  (algebra R).iInf (fun X : BV_name (Regular R) => (algebra R).imp
    (bv_mem (algebra R) X (omega (algebra R)))
    ((algebra R).iSup (fun Y : BV_name (Regular R) => (algebra R).meet
      (bv_mem (algebra R) Y (omega (algebra R)))
      ((algebra R).meet (above R X Y) (bv_mem (algebra R) Y G)))))

theorem atLeast_natural_of_le {i k : Nat} (h : i ≤ k) :
    atLeast R i (natural R k) = (algebra R).top := by
  unfold atLeast
  apply ((algebra R).top_le_iff _).mp
  rcases Nat.eq_or_lt_of_le h with he | hl
  · subst k
    have h := (algebra R).le_join_right
      (bv_mem (algebra R) (natural R i) (natural R i))
      (bv_eq (algebra R) (natural R i) (natural R i))
    simpa only [eq_refl] using h
  · have h := (algebra R).le_join_left
      (bv_mem (algebra R) (natural R i) (natural R k))
      (bv_eq (algebra R) (natural R i) (natural R k))
    rw [natural_mem_of_lt R hl] at h
    simpa only [natural_mem_of_lt R hl] using h

theorem atLeast_natural_of_lt {i k : Nat} (h : k < i) :
    atLeast R i (natural R k) = (algebra R).bot := by
  unfold atLeast
  rw [natural_mem_of_ge R (Nat.le_of_lt h), natural_eq_of_ne R (Nat.ne_of_gt h)]
  exact (algebra R).le_antisymm (((algebra R).join_le_iff _ _ _).mpr
    ⟨(algebra R).le_refl _, (algebra R).le_refl _⟩) ((algebra R).bot_le _)

theorem tail_as_exists (G : BV_name (Regular R)) (i : Nat) :
    (algebra R).iSup (fun Y : BV_name (Regular R) => (algebra R).meet
      (bv_mem (algebra R) Y (omega (algebra R)))
      ((algebra R).meet (atLeast R i Y) (bv_mem (algebra R) Y G))) = tailValue R G i := by
  rw [omega_sup R (fun Y => (algebra R).meet (atLeast R i Y) (bv_mem (algebra R) Y G))
    (stable_meet (algebra R) (above_right_stable R (natural R i))
    (stable_elem (algebra R) G))]
  apply (algebra R).le_antisymm
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro k
    by_cases h : i ≤ k
    · rw [atLeast_natural_of_le R h, (algebra R).top_meet]
      exact (algebra R).le_iSup
        (fun k : {k : Nat // i ≤ k} => bv_mem (algebra R) (natural R k.1) G) ⟨k, h⟩
    · rw [atLeast_natural_of_lt R (Nat.lt_of_not_ge h), (algebra R).bot_meet]
      exact (algebra R).bot_le _
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro k
    have h := (algebra R).le_iSup (fun n : Nat => (algebra R).meet
      (atLeast R i (natural R n)) (bv_mem (algebra R) (natural R n) G)) k.1
    rwa [atLeast_natural_of_le R k.2, (algebra R).top_meet] at h

theorem unbounded_eq_tails (G : BV_name (Regular R)) :
    unboundedValue R G = (algebra R).iInf (tailValue R G) := by
  unfold unboundedValue
  rw [omega_all R _ (stable_sup (algebra R) _ (fun Y =>
    stable_meet (algebra R) (stable_const (algebra R) _)
      (stable_meet (algebra R) (above_left_stable R Y) (stable_const (algebra R) _))))]
  apply congrArg (algebra R).iInf
  funext i
  exact tail_as_exists R G i

/-- Each lower bound has an actual natural-number name in G above it. The
maximum principle constructs the witnesses from the bounded formula value. -/
theorem unbounded_witnesses (G : BV_name (Regular R))
    (hG : unboundedValue R G = (algebra R).top) :
    ∃ f : Nat → BV_name (Regular R), ∀ i,
      bv_mem (algebra R) (f i) (omega (algebra R)) = (algebra R).top ∧
      atLeast R i (f i) = (algebra R).top ∧
      bv_mem (algebra R) (f i) G = (algebra R).top := by
  have ht (i : Nat) : tailValue R G i = (algebra R).top := by
    apply ((algebra R).top_le_iff _).mp
    rw [← hG, unbounded_eq_tails]
    exact (algebra R).iInf_le _ i
  have hex (i : Nat) : ∃ Y : BV_name (Regular R),
      bv_mem (algebra R) Y (omega (algebra R)) = (algebra R).top ∧
      atLeast R i Y = (algebra R).top ∧ bv_mem (algebra R) Y G = (algebra R).top := by
    let p (Y : BV_name (Regular R)) := (algebra R).meet
      (bv_mem (algebra R) Y (omega (algebra R)))
      ((algebra R).meet (atLeast R i Y) (bv_mem (algebra R) Y G))
    obtain ⟨Y, hY⟩ := maximum (algebra R) p
      (stable_meet (algebra R) (stable_elem (algebra R) _)
        (stable_meet (algebra R) (above_right_stable R (natural R i)) (stable_elem (algebra R) G)))
    have he : p Y = (algebra R).top := hY.trans ((tail_as_exists R G i).trans (ht i))
    have h := ((algebra R).le_meet_iff _ _ _).mp
      (show (algebra R).le (algebra R).top (p Y) from he ▸ (algebra R).le_refl _)
    have hh := ((algebra R).le_meet_iff _ _ _).mp h.2
    exact ⟨Y, ((algebra R).top_le_iff _).mp h.1,
      ((algebra R).top_le_iff _).mp hh.1, ((algebra R).top_le_iff _).mp hh.2⟩
  exact Classical.axiomOfChoice hex

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

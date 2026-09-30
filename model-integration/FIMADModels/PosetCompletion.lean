import Formalizations.FIMAD.PosetRegular
import YesMetaZFC.Model.Boolean.Infinity

/-! The shared regular-open construction as an actual YesMetaZFC complete
Boolean algebra, and dense decisions for its actual graph names in omega. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC.Model.Boolean
universe u v
variable {P : Type u} (R : Order P)

def algebra : CB_alg (Regular R) where
  le := Regular.Le
  bot := Regular.bot
  le_refl := Regular.le_refl
  le_trans := fun h k => Regular.le_trans _ _ _ h k
  le_antisymm := fun h k => Regular.le_antisymm _ _ h k
  bot_le _ _ h := False.elim h
  meet := Regular.meet
  imp := Regular.imp
  le_meet_iff := Regular.le_meet_iff
  le_imp_iff := Regular.le_imp_iff
  double_neg := Regular.double_neg
  sup := Regular.sup
  sup_le_iff S U := Regular.sup_le_iff U S

theorem algebra_top : (algebra R).top = Regular.top := by
  apply Regular.ext
  intro p
  exact ⟨fun _ => True.intro, fun _ _ _ h => False.elim h⟩

theorem algebra_iSup {I : Sort v} (f : I → Regular R) :
    (algebra R).iSup f = Regular.iSup f := by
  apply Regular.le_antisymm
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro i
    exact (Regular.iSup_le_iff _ f).mp (Regular.le_refl _) i
  · apply (Regular.iSup_le_iff _ f).mpr
    exact (algebra R).le_iSup f

/-- Actual ground natural numbers in the graph-name universe. -/
def natural (k : Nat) : BV_name (Regular R) :=
  BV_graph.omega_piece (algebra R) (List.replicate k PUnit.unit)

theorem omega_mem_eq (G : BV_name (Regular R)) :
    BV_graph.bv_mem (algebra R) G (BV_graph.omega (algebra R)) =
      (algebra R).iSup (fun k : Nat => BV_graph.bv_eq (algebra R) G (natural R k)) := by
  apply (algebra R).le_antisymm
  · apply ((algebra R).iSup_le_iff _ _).mpr
    rintro ⟨a, ha⟩
    cases a with
    | none => exact False.elim ha
    | some a =>
      have he : a = List.replicate a.length PUnit.unit :=
        List.ext_getElem (by simp) (fun _ _ _ => Subsingleton.elim _ _)
      apply (algebra R).le_trans ((algebra R).meet_le_right _ _)
      change (algebra R).le
        (BV_graph.bv_eq (algebra R) G (BV_graph.omega_piece (algebra R) a)) _
      rw [he]
      exact (algebra R).le_iSup
        (fun k : Nat => BV_graph.bv_eq (algebra R) G (natural R k)) a.length
  · apply ((algebra R).iSup_le_iff _ _).mpr
    intro k
    have h := BV_graph.mem_intro (algebra R) G (BV_graph.omega (algebra R))
      ⟨some (List.replicate k PUnit.unit), True.intro⟩
    simpa only [natural, BV_graph.omega_piece, BV_graph.omega, BA_alg.top_meet] using h

/-- A graph name forced to be a natural number can be decided below every
condition. The truth values here are BV_graph.bv_eq, not a supplied relation. -/
theorem natural_decisions_dense (G : BV_name (Regular R))
    (hG : BV_graph.bv_mem (algebra R) G (BV_graph.omega (algebra R)) = (algebra R).top) :
    ∀ p, ∃ q, R.le q p ∧ ∃ k,
      (BV_graph.bv_eq (algebra R) G (natural R k)).mem q := by
  apply (Regular.iSup_eq_top_iff _).mp
  rw [omega_mem_eq, algebra_iSup, algebra_top] at hG
  exact hG

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

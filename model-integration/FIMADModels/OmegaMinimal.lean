import FIMADModels.UnboundedTruth

/-! The actual omega graph is the least inductive set at full Boolean value,
with the exact OmegaFormula used by the FI MAD sentence. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Model YesMetaZFC.Model.Boolean BV_graph TypedModels
open SetTheory.Definitional.Project
universe u
variable {P : Type u} (R : Order P)

def emptyValue (E : BV_name (Regular R)) : Regular R :=
  (algebra R).iInf (fun X : BV_name (Regular R) => (algebra R).neg (bv_mem (algebra R) X E))

def inductiveValue (G : BV_name (Regular R)) : Regular R :=
  (algebra R).meet
    ((algebra R).iSup (fun E : BV_name (Regular R) =>
      (algebra R).meet (emptyValue R E) (bv_mem (algebra R) E G)))
    ((algebra R).iInf (fun X : BV_name (Regular R) => (algebra R).imp
      (bv_mem (algebra R) X G) ((algebra R).iSup (fun Y : BV_name (Regular R) =>
        (algebra R).meet (successor_value (algebra R) X Y) (bv_mem (algebra R) Y G)))))

theorem natural_zero_empty (X : BV_name (Regular R)) :
    bv_mem (algebra R) X (natural R 0) = (algebra R).bot := by
  unfold natural
  rw [omega_piece_mem]
  exact (algebra R).le_antisymm (((algebra R).iSup_le_iff _ _).mpr
    (fun b => False.elim (Nat.not_lt_zero _ b.2))) ((algebra R).bot_le _)

theorem empty_eq_zero (E : BV_name (Regular R)) :
    (algebra R).le (emptyValue R E) (bv_eq (algebra R) E (natural R 0)) := by
  apply le_eq_of_mem
  · intro X
    rw [natural_zero_empty]
    exact (algebra R).imp_use ((algebra R).le_trans ((algebra R).meet_le_left _ _)
      ((algebra R).iInf_le _ X)) ((algebra R).meet_le_right _ _)
  · intro X
    rw [natural_zero_empty, (algebra R).meet_bot]
    exact (algebra R).bot_le _

theorem natural_step_mem (n : Nat) (X : BV_name (Regular R)) :
    bv_mem (algebra R) X (natural R (n + 1)) = (algebra R).join
      (bv_mem (algebra R) X (natural R n)) (bv_eq (algebra R) X (natural R n)) := by
  simpa only [natural, List.replicate_succ] using
    omega_piece_step (algebra R) (List.replicate n PUnit.unit) X

theorem successor_eq_next (n : Nat) (Y : BV_name (Regular R)) :
    (algebra R).le (successor_value (algebra R) (natural R n) Y)
      (bv_eq (algebra R) Y (natural R (n + 1))) := by
  have h (X : BV_name (Regular R)) := (algebra R).iInf_le
    (fun X : BV_name (Regular R) => (algebra R).iff (bv_mem (algebra R) X Y)
      ((algebra R).join (bv_mem (algebra R) X (natural R n))
        (bv_eq (algebra R) X (natural R n)))) X
  apply le_eq_of_mem
  · intro X
    rw [natural_step_mem]
    exact (algebra R).imp_use ((algebra R).le_trans ((algebra R).meet_le_left _ _)
      ((algebra R).le_trans (h X) ((algebra R).meet_le_left _ _)))
      ((algebra R).meet_le_right _ _)
  · intro X
    rw [natural_step_mem]
    exact (algebra R).imp_use ((algebra R).le_trans ((algebra R).meet_le_left _ _)
      ((algebra R).le_trans (h X) ((algebra R).meet_le_right _ _)))
      ((algebra R).meet_le_right _ _)

theorem inductive_contains_natural (G : BV_name (Regular R)) (n : Nat) :
    (algebra R).le (inductiveValue R G) (bv_mem (algebra R) (natural R n) G) := by
  induction n with
  | zero =>
    apply (algebra R).le_trans ((algebra R).meet_le_left _ _)
    apply ((algebra R).iSup_le_iff _ _).mpr
    intro E
    exact (algebra R).le_trans ((algebra R).meet_mono (empty_eq_zero R E)
      ((algebra R).le_refl _)) (mem_left (algebra R) E (natural R 0) G)
  | succ n ih =>
    have hs : (algebra R).le (inductiveValue R G)
        ((algebra R).iSup (fun Y : BV_name (Regular R) => (algebra R).meet
          (successor_value (algebra R) (natural R n) Y) (bv_mem (algebra R) Y G))) :=
      (algebra R).imp_use ((algebra R).le_trans ((algebra R).meet_le_right _ _)
        ((algebra R).iInf_le _ (natural R n))) ih
    apply (algebra R).le_trans hs
    apply ((algebra R).iSup_le_iff _ _).mpr
    intro Y
    exact (algebra R).le_trans ((algebra R).meet_mono (successor_eq_next R n Y)
      ((algebra R).le_refl _)) (mem_left (algebra R) Y (natural R (n + 1)) G)

theorem omega_minimal (G : BV_name (Regular R)) :
    (algebra R).le (inductiveValue R G) (subset (algebra R) (omega (algebra R)) G) := by
  unfold subset
  rw [omega_all R _ (stable_elem (algebra R) G)]
  exact ((algebra R).le_iInf_iff _ _).mpr (inductive_contains_natural R G)

theorem omega_inductive : inductiveValue R (omega (algebra R)) = (algebra R).top := by
  apply ((algebra R).top_le_iff _).mp
  apply (algebra R).le_meet
  · obtain ⟨E, hE, hmem⟩ := (infinity (algebra R)).1
    have he : emptyValue R E = (algebra R).top := by
      apply ((algebra R).top_le_iff _).mp
      apply ((algebra R).le_iInf_iff _ _).mpr
      intro X
      rw [hE X]
      exact (algebra R).le_refl _
    have h := (algebra R).le_iSup (fun E : BV_name (Regular R) =>
      (algebra R).meet (emptyValue R E) (bv_mem (algebra R) E (omega (algebra R)))) E
    simpa only [he, hmem, BA_alg.meet_top] using h
  · exact (infinity (algebra R)).2

theorem project_empty_value {n : Nat} (env : BV_project.Env (algebra R) n)
    (a : SetTheory.Definitional.Project.Term n) :
    BV_project.value (algebra R) (Internal.Syntax.EmptyFormula a) env = emptyValue R (a.eval env) := by
  simp only [Internal.Syntax.EmptyFormula, BV_project.value, Definitional.Term.eval_weaken]
  rfl

theorem project_successor_value {n : Nat} (env : BV_project.Env (algebra R) n)
    (b a : SetTheory.Definitional.Project.Term n) :
    BV_project.value (algebra R) (Internal.Syntax.SuccFormula b a) env =
      successor_value (algebra R) (a.eval env) (b.eval env) := by
  simp only [Internal.Syntax.SuccFormula, Formula.extensionalEq, Formula.pairArguments_get_zero, Formula.pairArguments_get_one,
    BV_project.value, Definitional.Term.eval_weaken]
  rfl

theorem project_inductive_value {n : Nat} (env : BV_project.Env (algebra R) n)
    (a : SetTheory.Definitional.Project.Term n) :
    BV_project.value (algebra R) (Internal.Syntax.InductiveFormula a) env =
      inductiveValue R (a.eval env) := by
  simp only [Internal.Syntax.InductiveFormula, BV_project.value, project_empty_value,
    project_successor_value, Definitional.Term.eval_weaken]
  rfl

theorem project_omega_value {n : Nat} (env : BV_project.Env (algebra R) n)
    (w : SetTheory.Definitional.Project.Term n) (hw : w.eval env = omega (algebra R)) :
    BV_project.value (algebra R) (Internal.Syntax.OmegaFormula w) env = (algebra R).top := by
  simp only [Internal.Syntax.OmegaFormula, BV_project.value, project_inductive_value,
    Internal.Syntax.SubsetFormula, Definitional.Term.eval_weaken]
  change (algebra R).meet (inductiveValue R (w.eval env))
    ((algebra R).iInf (fun G : BV_name (Regular R) => (algebra R).imp (inductiveValue R G)
      (subset (algebra R) (w.eval env) G))) = _
  rw [hw, omega_inductive, (algebra R).top_meet]
  apply ((algebra R).top_le_iff _).mp
  apply ((algebra R).le_iInf_iff _ _).mpr
  intro G
  exact ((algebra R).valid_imp_iff _ _).mpr (omega_minimal R G)

abbrev omegaTyped := fo_formula (Internal.Syntax.OmegaFormula (.bound 0 : SetTheory.Definitional.Project.Term 1))
  (Internal.Syntax.closed_OmegaFormula _ rfl)

def omegaEnv : YesMetaZFC.Logic.FirstOrder.Env (BooleanQuotient.rawStructure (algebra R))
    (fo_bound_context 1) [] := Env.empty.pushBound (omega (algebra R))

theorem typed_omega_value :
    BV_str.value (algebra R) (name_structure (algebra R)) omegaTyped (omegaEnv R) = (algebra R).top := by
  rw [BV_project.formula_correct (algebra R) _ (Internal.Syntax.closed_OmegaFormula _ rfl)
    (omegaEnv R) (fun _ => BV_graph.empty (algebra R).toPO_bot)]
  exact project_omega_value R _ _ rfl

theorem quotient_omega (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l) :
    Internal.Omega (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) := by
  have ht := BooleanQuotient.truth (algebra R) U hU omegaTyped (omegaEnv R)
  rw [typed_omega_value] at ht
  have hn := FirstOrderSemantics.formula_correct (BooleanQuotient.extensional (algebra R) U hU)
    (Internal.Syntax.OmegaFormula (.bound 0 : SetTheory.Definitional.Project.Term 1)) (Internal.Syntax.closed_OmegaFormula _ rfl)
    ((omegaEnv R).map (BooleanQuotient.quotientMap (algebra R) U).map)
    (fun _ => BooleanQuotient.classOf (algebra R) U (BV_graph.empty (algebra R).toPO_bot))
  have hs := Internal.Syntax.satisfies_OmegaFormula (BooleanQuotient.extensional (algebra R) U hU)
    (FirstOrderSemantics.projectEnv ((omegaEnv R).map (BooleanQuotient.quotientMap (algebra R) U).map)
      (fun _ => BooleanQuotient.classOf (algebra R) U (BV_graph.empty (algebra R).toPO_bot))) (.bound 0)
  exact (hn.trans hs).mp (ht.mpr U.top_mem)

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

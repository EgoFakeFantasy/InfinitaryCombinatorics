import FIMADModels.SplittingNames
import FIMADModels.BooleanQuotient
import Formalizations.FIMAD.UnboundedSyntax

/-! Exact first-order meaning and ordinary-quotient truth for the bounded
unboundedness value used in the graph-name splitting theorem. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Model YesMetaZFC.Model.Boolean BV_graph
open SetTheory.Definitional.Project
open TypedModels
universe u
variable {P : Type u} (R : Order P)

theorem project_unbounded_value {n : Nat} (env : BV_project.Env (algebra R) n)
    (w a : SetTheory.Definitional.Project.Term n) :
    BV_project.value (algebra R) (Internal.Syntax.UnboundedFormula w a) env =
      (algebra R).iInf (fun X : BV_name (Regular R) => (algebra R).imp
        (bv_mem (algebra R) X (w.eval env))
        ((algebra R).iSup (fun Y : BV_name (Regular R) => (algebra R).meet
          (bv_mem (algebra R) Y (w.eval env))
          ((algebra R).meet (above R X Y) (bv_mem (algebra R) Y (a.eval env)))))) := by
  simp only [Internal.Syntax.UnboundedFormula, BV_project.value,
    Definitional.Term.eval_weaken]
  rfl

abbrev unboundedTyped := fo_formula Internal.Syntax.unboundedBody Internal.Syntax.unboundedBody_closed

def unboundedEnv (G : BV_name (Regular R)) :
    YesMetaZFC.Logic.FirstOrder.Env (BooleanQuotient.rawStructure (algebra R))
      (fo_bound_context 2) [] :=
  (Env.empty.pushBound (omega (algebra R))).pushBound G

theorem typed_unbounded_value (G : BV_name (Regular R)) :
    BV_str.value (algebra R) (name_structure (algebra R)) unboundedTyped (unboundedEnv R G) =
      unboundedValue R G := by
  rw [BV_project.formula_correct (algebra R) _ Internal.Syntax.unboundedBody_closed
    (unboundedEnv R G) (fun _ => BV_graph.empty (algebra R).toPO_bot)]
  change BV_project.value (algebra R) (Internal.Syntax.UnboundedFormula (.bound 1) (.bound 0)) _ = _
  rw [project_unbounded_value]
  rfl

theorem quotient_unbounded_iff (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (G : BV_name (Regular R)) :
    Internal.Unbounded (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))
      (BooleanQuotient.classOf (algebra R) U G) ↔ U.mem (unboundedValue R G) := by
  have ht := BooleanQuotient.truth (algebra R) U hU unboundedTyped (unboundedEnv R G)
  rw [typed_unbounded_value] at ht
  have hn := FirstOrderSemantics.formula_correct (BooleanQuotient.extensional (algebra R) U hU)
    Internal.Syntax.unboundedBody Internal.Syntax.unboundedBody_closed
    ((unboundedEnv R G).map (BooleanQuotient.quotientMap (algebra R) U).map)
    (fun _ => BooleanQuotient.classOf (algebra R) U (BV_graph.empty (algebra R).toPO_bot))
  have hs := Internal.Syntax.satisfies_UnboundedFormula
    (BooleanQuotient.extensional (algebra R) U hU)
    (FirstOrderSemantics.projectEnv
      ((unboundedEnv R G).map (BooleanQuotient.quotientMap (algebra R) U).map)
      (fun _ => BooleanQuotient.classOf (algebra R) U (BV_graph.empty (algebra R).toPO_bot)))
    (.bound 1) (.bound 0)
  exact (hn.trans hs).symm.trans ht

/-- Top-valued unboundedness holds in every maximal-filter quotient, without
assuming that the quotient has only standard natural numbers. -/
theorem quotient_unbounded_of_top (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (G : BV_name (Regular R)) (hG : unboundedValue R G = (algebra R).top) :
    Internal.Unbounded (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))
      (BooleanQuotient.classOf (algebra R) U G) :=
  (quotient_unbounded_iff R U hU G).mpr (hG ▸ U.top_mem)

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

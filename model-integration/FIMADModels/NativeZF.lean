import FIMADModels.BooleanQuotient
import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.SetTheory.Axioms.ZF

/-! Expose the ordinary quotient to the upstream native ZF theorem API. -/
set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.Model.Boolean
open Definitional.Project
universe u
variable {B : Type u} (𝔹 : CB_alg B) (U : Filter_l 𝔹.toBA_alg)

theorem models_native_zf (hU : U.Maximal_l) :
    (FirstOrderSemantics.reduct (quotientStructure 𝔹 U)).Models SetTheory.ZF := by
  have hc := (FirstOrderSemantics.models_iff (extensional 𝔹 U hU) CheckedZFC.Axiom).mp
    (models_zfc 𝔹 U hU)
  refine ⟨hc.1, ?_⟩
  intro s hs
  apply hc.2 s
  cases hs with
  | extensionality => exact CheckedZFC.Axiom.extensionality
  | emptySet => exact CheckedZFC.Axiom.emptySet
  | pairing => exact CheckedZFC.Axiom.pairing
  | union => exact CheckedZFC.Axiom.union
  | powerSet => exact CheckedZFC.Axiom.powerSet
  | infinity => exact CheckedZFC.Axiom.infinity
  | foundation => exact CheckedZFC.Axiom.foundation
  | separation φ => exact CheckedZFC.Axiom.separation φ
  | collection φ => exact CheckedZFC.Axiom.collection φ

end InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient

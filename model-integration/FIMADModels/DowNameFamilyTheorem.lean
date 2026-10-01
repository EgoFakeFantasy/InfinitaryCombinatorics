import FIMADModels.DowNameFamily

/-! The original ZFC kernel proves simultaneous tallness tests for every
internally countable family of actual unbounded forcing names. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def unboundedNameFamilyFormula {n} (B R W L : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest L.weaken)
    (.conj (name_m B.weaken .newest)
      (forcesUnboundedNameFormula B.weaken R.weaken W.weaken .newest)))

def nameFamilyTestsFormula {n} (w A B R c L H : Project.Term n) : Project.Formula 1 n :=
  .conj (.existsE (Internal.Syntax.InjectionFormula .newest H.weaken w.weaken))
    (.conj (.forallE (.imp (.mem .newest H.weaken) (Internal.Syntax.SubsetFormula .newest w.weaken)))
      (.forallE (.imp (.mem .newest L.weaken)
        (.existsE (.conj
          (membershipDecisionsFormula w.weaken.weaken B.weaken.weaken R.weaken.weaken
            c.weaken.weaken (.bound 1) .newest)
          (.forallE (.imp (meetsTestsFormula w.weaken.weaken.weaken .newest H.weaken.weaken.weaken)
            (tallDensityFormula w.weaken.weaken.weaken A.weaken.weaken.weaken (.bound 1) .newest))))))))

derive_free_closed unboundedNameFamilyFormula
derive_free_closed nameFamilyTestsFormula

theorem unboundedNameFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R W L : Project.Term n) : Project.Formula.satisfies ρ (unboundedNameFamilyFormula B R W L) ↔
      ∀ t, M.mem t (L.eval ρ) → Name_d M (B.eval ρ) t ∧
        ForcesUnboundedName (B.eval ρ) (R.eval ρ) (W.eval ρ) t := by
  simp only [unboundedNameFamilyFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff, name_sat_l M hE, forcesUnboundedNameFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem nameFamilyTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A B R c L H : Project.Term n) : Project.Formula.satisfies ρ (nameFamilyTestsFormula w A B R c L H) ↔
      NameFamilyTests (w.eval ρ) (A.eval ρ) (B.eval ρ) (R.eval ρ) (c.eval ρ) (L.eval ρ) (H.eval ρ) := by
  simp only [nameFamilyTestsFormula, NameFamilyTests, InternalCountable,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_exists_iff,
    Internal.Syntax.satisfies_InjectionFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_SubsetFormula hE, membershipDecisionsFormula_semantics hE,
    meetsTestsFormula_semantics hE, tallDensityFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def nameFamilyTestsBody : Project.Formula 1 7 :=
  .imp (Project.Formula.isOmega (.bound 6))
    (.imp (carrierFormula (.bound 6) (.bound 5) (.bound 4))
      (.imp (orderFormula (.bound 4) (.bound 3))
        (.imp (cond_order_m (.bound 4) (.bound 3) (.bound 4))
          (.imp (topFormula (.bound 4) (.bound 3) (.bound 2))
            (.imp (check_m (.bound 2) (.bound 6) (.bound 1))
              (.imp (.existsE (Internal.Syntax.InjectionFormula .newest (.bound 1) (.bound 7)))
                (.imp (unboundedNameFamilyFormula (.bound 4) (.bound 3) (.bound 1) .newest)
                  (.existsE (nameFamilyTestsFormula (.bound 7) (.bound 6) (.bound 5)
                    (.bound 4) (.bound 3) (.bound 1) .newest)))))))))

theorem nameFamilyTestsBody_closed : nameFamilyTestsBody.FreeClosed := by
  simp -implicitDefEqProofs [nameFamilyTestsBody, Definitional.Formula.FreeClosed]

def nameFamilyTestsSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose nameFamilyTestsBody)
  (ObjectTheory.universalClose_closed _ nameFamilyTestsBody_closed)

theorem nameFamilyTestsBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 7) :
    Project.Formula.satisfies ρ nameFamilyTestsBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [nameFamilyTestsBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    carrierFormula_semantics hZF.1, orderFormula_semantics hZF.1, cond_order_sat_l hZF.1,
    topFormula_semantics hZF.1, check_sat_l M hZF.1, Project.Formula.satisfies_exists_iff,
    Internal.Syntax.satisfies_InjectionFormula hZF.1, unboundedNameFamilyFormula_semantics hZF.1,
    nameFamilyTestsFormula_semantics hZF.1]
  intro hw hB hR O hc hW hLc hNames
  exact countable_name_tests_exists hZFC hw O hB hR hc.1 hc.2 hW hLc hNames
end Syntax

theorem derives_countable_name_tests : Project.Derives SetTheory.ZFC Syntax.nameFamilyTestsSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.nameFamilyTestsBody (Syntax.nameFamilyTestsBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

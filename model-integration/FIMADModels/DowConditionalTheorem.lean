import FIMADModels.DowConditionalPreservation

/-! Original ZFC derivation of the localized countable-name preservation
theorem. Names need not be globally forced to be infinite or to be reals. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def actualNameFamilyFormula {n} (B L : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest L.weaken) (name_m B.weaken .newest))

derive_free_closed actualNameFamilyFormula

theorem actualNameFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B L : Project.Term n) : Project.Formula.satisfies ρ (actualNameFamilyFormula B L) ↔
      ∀ t, M.mem t (L.eval ρ) → Name_d M (B.eval ρ) t := by
  simp only [actualNameFamilyFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    name_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def splitsInfiniteNamesFormula {n} (B R W L bs : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest L.weaken) (.forallE (.imp (.mem .newest B.weaken.weaken)
    (.imp (forceInfiniteRealFormula B.weaken.weaken R.weaken.weaken B.weaken.weaken
      W.weaken.weaken (.bound 1) .newest)
      (force_at_m (splitsSetFormula (.bound 2) (.bound 1) .newest : Project.Formula 1 3)
        (Fin.cases bs.weaken.weaken (Fin.cases (.bound 1) (fun _ => W.weaken.weaken)))
        B.weaken.weaken R.weaken.weaken B.weaken.weaken .newest)))))

@[simp] theorem splitsInfiniteNamesFormula_closed {n} (B R W L bs : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hW : W.freeSupport = [])
    (hL : L.freeSupport = []) (hbs : bs.freeSupport = []) :
    (splitsInfiniteNamesFormula B R W L bs).FreeClosed := by
  simp only [splitsInfiniteNamesFormula, Definitional.Formula.FreeClosed]
  refine ⟨⟨rfl, by simpa using hL⟩, ⟨rfl, by simpa using hB⟩, ?_, ?_⟩
  · exact forceInfiniteRealFormula_closed _ _ _ _ _ _ (by simpa using hB)
      (by simpa using hR) (by simpa using hB) (by simpa using hW) rfl rfl
  · apply force_at_closed_l
    · exact splitsSetFormula_freeClosed _ _ _ rfl rfl rfl
    · exact Fin.cases (by simpa using hbs) (Fin.cases rfl (fun _ => by simpa using hW))
    · simpa using hB
    · simpa using hR
    · simpa using hB
    · rfl

theorem splitsInfiniteNamesFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R W L bs : Project.Term n) :
    Project.Formula.satisfies ρ (splitsInfiniteNamesFormula B R W L bs) ↔
      SplitsInfiniteNames (B.eval ρ) (R.eval ρ) (W.eval ρ) (L.eval ρ) (bs.eval ρ) := by
  simp only [splitsInfiniteNamesFormula, SplitsInfiniteNames,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, forceInfiniteRealFormula_semantics hE,
    force_at_sat_l, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply forces_env_l hE _ (splitsSetFormula_freeClosed _ _ _ rfl rfl rfl)
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) i
  · simp only [Fin.cases_zero, Definitional.Term.eval_weaken]
    rfl
  · rfl
  · simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
    rfl

def conditionalPreservationBody : Project.Formula 1 8 :=
  .imp (Project.Formula.isOmega (.bound 7))
    (.imp (carrierFormula (.bound 7) (.bound 6) (.bound 5))
      (.imp (orderFormula (.bound 5) (.bound 4))
        (.imp (cond_order_m (.bound 5) (.bound 4) (.bound 5))
          (.imp (topFormula (.bound 5) (.bound 4) (.bound 3))
            (.imp (check_m (.bound 3) (.bound 7) (.bound 2))
              (.imp (.existsE (Internal.Syntax.InjectionFormula .newest (.bound 2) (.bound 8)))
                (.imp (actualNameFamilyFormula (.bound 5) (.bound 1))
                  (.imp (omegaSplittingTestsFormula (.bound 7) .newest)
                    (.existsE (.existsE (.conj (.mem (.bound 1) (.bound 2))
                      (.conj (Internal.Syntax.SubsetFormula (.bound 1) (.bound 9))
                        (.conj (check_m (.bound 5) (.bound 1) .newest)
                          (splitsInfiniteNamesFormula (.bound 7) (.bound 6) (.bound 4) (.bound 3) .newest))))))))))))))

theorem conditionalPreservationBody_closed : conditionalPreservationBody.FreeClosed := by
  simp -implicitDefEqProofs [conditionalPreservationBody, Definitional.Formula.FreeClosed]

def conditionalPreservationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose conditionalPreservationBody)
  (ObjectTheory.universalClose_closed _ conditionalPreservationBody_closed)

theorem conditionalPreservationBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 8) :
    Project.Formula.satisfies ρ conditionalPreservationBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [conditionalPreservationBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, carrierFormula_semantics hZF.1,
    orderFormula_semantics hZF.1, cond_order_sat_l hZF.1, topFormula_semantics hZF.1,
    check_sat_l M hZF.1, Project.Formula.satisfies_exists_iff,
    Internal.Syntax.satisfies_InjectionFormula hZF.1, actualNameFamilyFormula_semantics hZF.1,
    omegaSplittingTestsFormula_semantics hZF.1, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Internal.Syntax.satisfies_SubsetFormula hZF.1,
    splitsInfiniteNamesFormula_semantics hZF.1]
  intro hw hB hR O hc hW hLc hNames hS
  exact preserves_countable_names hZFC hw O hB hR hc.1 hc.2 hW hLc hNames hS
end Syntax

theorem derives_conditional_countable_name_preservation :
    Project.Derives SetTheory.ZFC Syntax.conditionalPreservationSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid _ (Syntax.conditionalPreservationBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

import FIMADModels.DowNameTests

/-! Original-kernel ZFC endpoint for countable tests of actual forcing names.
The hypothesis is the translated unbounded-name formula, not an abstract
monotonicity or decision-density certificate. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def ForcesUnboundedName (B R W t : M.Domain) : Prop :=
  ∀ p, M.mem p B → Forces_d M B R B
    (Syntax.unboundedNameFormula (.bound 1) .newest)
    ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p

namespace Syntax
def membershipDecisionsFormula {n} (w B R c t E : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.iff (entry_m (.bound 1) .newest E.weaken.weaken)
    (.conj (.mem (.bound 1) B.weaken.weaken)
      (.conj (.mem .newest w.weaken.weaken)
        (membershipDecisionFormula B.weaken.weaken R.weaken.weaken c.weaken.weaken
          t.weaken.weaken (.bound 1) .newest)))))

def forcesUnboundedNameFormula {n} (B R W t : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest B.weaken)
    (force_at_m (unboundedNameFormula (.bound 1) .newest : Project.Formula 1 2)
      (Fin.cases t.weaken (fun _ => W.weaken)) B.weaken R.weaken B.weaken .newest))

derive_free_closed membershipDecisionsFormula
@[simp] theorem forcesUnboundedNameFormula_freeClosed {n} (B R W t : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (hW : W.freeSupport = []) (ht : t.freeSupport = []) :
    (forcesUnboundedNameFormula B R W t).FreeClosed := by
  simp only [forcesUnboundedNameFormula, Definitional.Formula.FreeClosed]
  refine ⟨⟨rfl, by simpa using hB⟩, ?_⟩
  apply force_at_closed_l
  · exact unboundedNameFormula_freeClosed _ _ rfl rfl
  · exact Fin.cases (by simpa using ht) (fun _ => by simpa using hW)
  · simpa using hB
  · simpa using hR
  · simpa using hB
  · rfl

theorem membershipDecisionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w B R c t E : Project.Term n) : Project.Formula.satisfies ρ (membershipDecisionsFormula w B R c t E) ↔
      MembershipDecisions (w.eval ρ) (B.eval ρ) (R.eval ρ) (c.eval ρ) (t.eval ρ) (E.eval ρ) := by
  simp only [membershipDecisionsFormula, MembershipDecisions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, entry_sat_l M hE, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, membershipDecisionFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem forcesUnboundedNameFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R W t : Project.Term n) : Project.Formula.satisfies ρ (forcesUnboundedNameFormula B R W t) ↔
      ForcesUnboundedName (B.eval ρ) (R.eval ρ) (W.eval ρ) (t.eval ρ) := by
  simp only [forcesUnboundedNameFormula, ForcesUnboundedName, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff, force_at_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  apply forces_env_l hE _ (unboundedNameFormula_freeClosed _ _ rfl rfl)
  intro i
  refine Fin.cases ?_ (fun _ => ?_) i
  · change t.weaken.eval (ρ.push p) = t.eval ρ
    simp only [Definitional.Term.eval_weaken]
  · change W.weaken.eval (ρ.push p) = W.eval ρ
    simp only [Definitional.Term.eval_weaken]

def nameTestsBody : Project.Formula 1 7 :=
  .imp (Project.Formula.isOmega (.bound 6))
    (.imp (carrierFormula (.bound 6) (.bound 5) (.bound 4))
      (.imp (orderFormula (.bound 4) (.bound 3))
        (.imp (cond_order_m (.bound 4) (.bound 3) (.bound 4))
          (.imp (topFormula (.bound 4) (.bound 3) (.bound 2))
            (.imp (name_m (.bound 4) (.bound 1))
              (.imp (check_m (.bound 2) (.bound 6) .newest)
                (.imp (forcesUnboundedNameFormula (.bound 4) (.bound 3) .newest (.bound 1))
                  (.existsE (.existsE (.conj
                    (membershipDecisionsFormula (.bound 8) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 1))
                    (tallTestsWitnessFormula (.bound 8) (.bound 7) (.bound 1) .newest)))))))))))

theorem nameTestsBody_closed : nameTestsBody.FreeClosed := by
  simp -implicitDefEqProofs [nameTestsBody, Definitional.Formula.FreeClosed]

def nameTestsSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose nameTestsBody) (ObjectTheory.universalClose_closed _ nameTestsBody_closed)

theorem nameTestsBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 7) :
    Project.Formula.satisfies ρ nameTestsBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [nameTestsBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    carrierFormula_semantics hZF.1, orderFormula_semantics hZF.1, cond_order_sat_l hZF.1,
    topFormula_semantics hZF.1, name_sat_l M hZF.1, check_sat_l M hZF.1,
    forcesUnboundedNameFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, membershipDecisionsFormula_semantics hZF.1,
    tallTestsWitnessFormula_semantics hZF.1]
  intro hw hB hR O hc ht hW hForce
  exact name_tall_tests_exists hZFC hw O hB hR hc.1 hc.2 ht hW hForce
end Syntax

theorem derives_name_tall_tests : Project.Derives SetTheory.ZFC Syntax.nameTestsSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.nameTestsBody (Syntax.nameTestsBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

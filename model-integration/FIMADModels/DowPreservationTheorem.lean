import FIMADModels.DowExtensionPreservation

/-! The original ZFC kernel proves actual single-step Dow preservation of
omega-splitting. Public finite-parameter reflection preserves ZFC, then the
public countable forcing criterion consumes the all-generic-quotient proof.
No preservation certificate, external standard omega, or ground enumeration
occurs in the final sentence. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def dowPreservationInput : Project.Formula 1 9 :=
  .conj (cond_order_m (.bound 6) (.bound 5) (.bound 6))
    (.conj (.mem .newest (.bound 6))
      (.conj (.neg (Project.Formula.extensionalEq .newest (.bound 6)))
        (.conj (Project.Formula.isOmega (.bound 8))
          (.conj (carrierFormula (.bound 8) (.bound 7) (.bound 6))
            (.conj (orderFormula (.bound 6) (.bound 5))
              (.conj (topFormula (.bound 6) (.bound 5) (.bound 4))
                (.conj (check_m (.bound 4) (.bound 8) (.bound 2))
                  (.conj (check_m (.bound 4) (.bound 3) (.bound 1))
                    (omegaSplittingTestsFormula (.bound 8) (.bound 3))))))))))

def dowPreservationConclusion : Project.Formula 1 9 :=
  force_at_m (omegaSplittingTestsFormula (.bound 1) .newest : Project.Formula 1 2)
    (Fin.cases (.bound 1) (fun _ => .bound 2)) (.bound 6) (.bound 5) (.bound 6) .newest

theorem dowPreservationInput_closed : dowPreservationInput.FreeClosed := by
  simp -implicitDefEqProofs [dowPreservationInput, Definitional.Formula.FreeClosed]

theorem dowPreservationConclusion_closed : dowPreservationConclusion.FreeClosed := by
  unfold dowPreservationConclusion
  apply force_at_closed_l
  · exact omegaSplittingTestsFormula_freeClosed _ _ rfl rfl
  · exact Fin.cases rfl (fun _ => rfl)
  all_goals rfl

theorem dowPreservationInput_semantics (hE : Extensional M) (ρ : Env M 9) :
    Project.Formula.satisfies ρ dowPreservationInput ↔
      Cond_order_d M (ρ.bound 6) (ρ.bound 5) (ρ.bound 6) ∧ M.mem (ρ.bound 0) (ρ.bound 6) ∧
      ρ.bound 0 ≠ ρ.bound 6 ∧ M.IsOmega (ρ.bound 8) ∧
      (∀ p, M.mem p (ρ.bound 6) ↔ CodedCondition (ρ.bound 8) (ρ.bound 7) p) ∧
      (∀ p q, Entry_d M p q (ρ.bound 5) ↔ M.mem p (ρ.bound 6) ∧ M.mem q (ρ.bound 6) ∧ CodedExtends (M := M) p q) ∧
      (M.mem (ρ.bound 4) (ρ.bound 6) ∧ ∀ p, M.mem p (ρ.bound 6) → Entry_d M p (ρ.bound 4) (ρ.bound 5)) ∧
      Check_d M (ρ.bound 4) (ρ.bound 8) (ρ.bound 2) ∧
      Check_d M (ρ.bound 4) (ρ.bound 3) (ρ.bound 1) ∧ OmegaSplittingTests (ρ.bound 8) (ρ.bound 3) := by
  simp only [dowPreservationInput, Project.Formula.satisfies_conj_iff, cond_order_sat_l hE,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, Project.Formula.satisfies_isOmega_iff,
    carrierFormula_semantics hE, orderFormula_semantics hE, topFormula_semantics hE,
    check_sat_l M hE, omegaSplittingTestsFormula_semantics hE]
  rfl
end Syntax

theorem forces_dow_preservation (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 9)
    (hInput : Project.Formula.satisfies ρ Syntax.dowPreservationInput) :
    Project.Formula.satisfies ρ Syntax.dowPreservationConclusion := by
  apply FirstOrderSemantics.countable_consequence_l (Γ := SetTheory.ZFC)
    Syntax.dowPreservationInput Syntax.dowPreservationConclusion
    Syntax.dowPreservationInput_closed Syntax.dowPreservationConclusion_closed ?_ hZFC ρ hInput
  intro K hKC enum hEnum η hα
  let hK := ZFC.models_zf_l hKC
  obtain ⟨O, hp, hz, hw, hB, hR, hc, hW, hS, hSplit⟩ :=
    (Syntax.dowPreservationInput_semantics hK.1 η).mp hα
  apply (force_at_sat_l _ η (Fin.cases (.bound 1) (fun _ => .bound 2))
    (.bound 6) (.bound 5) (.bound 6) .newest).mpr
  let args : Fin 2 → Project.Term 9 := Fin.cases (.bound 1) (fun _ => .bound 2)
  have names : ∀ i : Fin 2, Name_d K (η.bound 6) ((args i).eval η) := by
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact check_name_l K (check_range_l K hK) hc.1 hS
    · exact check_name_l K (check_range_l K hK) hc.1 hW
  apply forces_countable_l O hK enum hEnum
    (Syntax.omegaSplittingTestsFormula (.bound 1) .newest : Project.Formula 1 2)
    (Syntax.omegaSplittingTestsFormula_freeClosed _ _ rfl rfl)
    (⟨fun i => (args i).eval η, η.free⟩ : Env K 2) names hp hz
  intro U hU hpU ξ hξ
  have hcU := hU.upward _ _ hpU hc.1 (hc.2 _ (hU.proper _ hpU).1)
  obtain ⟨e, hv, he, hi⟩ := check_map_l O hK hU hcU
  have heW : e (η.bound 8) = ξ.bound 1 := qval_unique_l (hv _ _ hW) (hξ 1)
  have heS : e (η.bound 3) = ξ.bound 0 := qval_unique_l (hv _ _ hS) (hξ 0)
  have hResult := omega_splitting_in_extension hKC O hU hw hB hR hc.1 hc.2 hW hSplit e hi he hv
  apply (Syntax.omegaSplittingTestsFormula_semantics (preserves_zf_l O hK hU).1 ξ (.bound 1) .newest).mpr
  change OmegaSplittingTests (M := extension_l K hK (η.bound 6) (η.bound 5) (η.bound 6) U)
    (ξ.bound 1) (ξ.bound 0)
  rwa [heW, heS] at hResult

namespace Syntax
def dowPreservationBody : Project.Formula 1 9 := .imp dowPreservationInput dowPreservationConclusion

theorem dowPreservationBody_closed : dowPreservationBody.FreeClosed := by
  simp only [dowPreservationBody, Definitional.Formula.FreeClosed]
  exact ⟨dowPreservationInput_closed, dowPreservationConclusion_closed⟩

def dowPreservationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose dowPreservationBody)
  (ObjectTheory.universalClose_closed _ dowPreservationBody_closed)

theorem dowPreservationBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 9) :
    Project.Formula.satisfies ρ dowPreservationBody :=
  (Project.Formula.satisfies_imp_iff ρ _ _).mpr (forces_dow_preservation hZFC ρ)
end Syntax

theorem derives_dow_omega_splitting_preservation :
    Project.Derives SetTheory.ZFC Syntax.dowPreservationSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid _ (Syntax.dowPreservationBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

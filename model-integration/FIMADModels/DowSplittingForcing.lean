import FIMADModels.DowSplittingSyntax

/-! A genuine forcing statement, obtained from all internal generic quotients
using the public finite-parameter reflection criterion. The final theorem is
in the original Project derivation kernel; no external countability premise
or abstract preservation certificate occurs in its sentence. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def splittingInput : Project.Formula 1 12 :=
  .conj (Project.Formula.isOmega (.bound 11))
    (.conj (carrierFormula (.bound 11) (.bound 10) (.bound 9))
      (.conj (orderFormula (.bound 9) (.bound 8))
        (.conj (topFormula (.bound 9) (.bound 8) (.bound 7))
          (.conj (nameFamilyTestsFormula (.bound 11) (.bound 10) (.bound 9) (.bound 8)
            (.bound 7) (.bound 6) (.bound 5))
            (.conj (.mem (.bound 3) (.bound 6))
              (.conj (Internal.Syntax.SubsetFormula (.bound 4) (.bound 11))
                (.conj (splitsTestsFormula (.bound 11) (.bound 4) (.bound 5))
                  (.conj (check_m (.bound 7) (.bound 11) (.bound 2))
                    (.conj (check_m (.bound 7) (.bound 4) (.bound 1))
                      (.conj (name_m (.bound 9) (.bound 3))
                        (force_at_m (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
                          (Fin.cases (.bound 2) (fun _ => .bound 3))
                          (.bound 9) (.bound 8) (.bound 9) .newest)))))))))))

theorem splittingInput_closed : splittingInput.FreeClosed := by
  simp -implicitDefEqProofs [splittingInput, Definitional.Formula.FreeClosed]
  apply force_at_closed_l
  · exact (Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩
  · exact Fin.cases rfl (fun _ => rfl)
  all_goals rfl

theorem splittingInput_semantics {K : SetTheory.Structure.{u}} (hE : Extensional K) (ρ : Env K 12) :
    Project.Formula.satisfies ρ splittingInput ↔
      K.IsOmega (ρ.bound 11) ∧
      (∀ p, K.mem p (ρ.bound 9) ↔ CodedCondition (ρ.bound 11) (ρ.bound 10) p) ∧
      (∀ p q, Entry_d K p q (ρ.bound 8) ↔ K.mem p (ρ.bound 9) ∧ K.mem q (ρ.bound 9) ∧ CodedExtends (M := K) p q) ∧
      (K.mem (ρ.bound 7) (ρ.bound 9) ∧ ∀ p, K.mem p (ρ.bound 9) → Entry_d K p (ρ.bound 7) (ρ.bound 8)) ∧
      NameFamilyTests (ρ.bound 11) (ρ.bound 10) (ρ.bound 9) (ρ.bound 8) (ρ.bound 7) (ρ.bound 6) (ρ.bound 5) ∧
      K.mem (ρ.bound 3) (ρ.bound 6) ∧ Internal.Subset K.mem (ρ.bound 4) (ρ.bound 11) ∧
      SplitsTests (ρ.bound 11) (ρ.bound 4) (ρ.bound 5) ∧ Check_d K (ρ.bound 7) (ρ.bound 11) (ρ.bound 2) ∧
      Check_d K (ρ.bound 7) (ρ.bound 4) (ρ.bound 1) ∧ Name_d K (ρ.bound 9) (ρ.bound 3) ∧
      Forces_d K (ρ.bound 9) (ρ.bound 8) (ρ.bound 9)
        (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
        (⟨fun i => (Fin.cases (.bound 2) (fun _ => .bound 3) i : Project.Term 12).eval ρ, ρ.free⟩ : Env K 2)
        (ρ.bound 0) := by
  simp only [splittingInput, Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isOmega_iff,
    carrierFormula_semantics hE, orderFormula_semantics hE, topFormula_semantics hE,
    nameFamilyTestsFormula_semantics hE, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_SubsetFormula hE, splitsTestsFormula_semantics hE,
    check_sat_l K hE, name_sat_l K hE, force_at_sat_l]
  rfl

def splittingArguments : Fin 3 → Project.Term 12 :=
  Fin.cases (.bound 1) (Fin.cases (.bound 3) (fun _ => .bound 2))

def splittingConclusion : Project.Formula 1 12 :=
  force_at_m (splitsSetFormula (.bound 2) (.bound 1) .newest : Project.Formula 1 3)
    splittingArguments (.bound 9) (.bound 8) (.bound 9) .newest

theorem splittingConclusion_closed : splittingConclusion.FreeClosed := by
  apply force_at_closed_l
  · exact splitsSetFormula_freeClosed _ _ _ rfl rfl rfl
  · exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  all_goals rfl
end Syntax

theorem forces_splitting_from_tests (hZF : M.Models SetTheory.ZF) (ρ : Env M 12)
    (O : Cond_order_d M (ρ.bound 9) (ρ.bound 8) (ρ.bound 9))
    (hp : M.mem (ρ.bound 0) (ρ.bound 9)) (hz : ρ.bound 0 ≠ ρ.bound 9)
    (hInput : Project.Formula.satisfies ρ Syntax.splittingInput) :
    Project.Formula.satisfies ρ Syntax.splittingConclusion := by
  obtain ⟨_, _, _, hc, _, _, _, _, hW, hb, ht, _⟩ := (Syntax.splittingInput_semantics hZF.1 ρ).mp hInput
  have names : ∀ i, Name_d M (ρ.bound 9) ((Syntax.splittingArguments i).eval ρ) :=
    Fin.cases (check_name_l M (check_range_l M hZF) hc.1 hb)
      (Fin.cases ht (fun _ => check_name_l M (check_range_l M hZF) hc.1 hW))
  apply (force_at_sat_l _ ρ Syntax.splittingArguments (.bound 9) (.bound 8) (.bound 9) .newest).mpr
  apply forces_of_generics_l
    (Syntax.splitsSetFormula (.bound 2) (.bound 1) .newest : Project.Formula 1 3)
    (Syntax.splitsSetFormula_freeClosed _ _ _ rfl rfl rfl)
    Syntax.splittingInput Syntax.splittingInput_closed Syntax.splittingArguments
    (.bound 9) (.bound 8) (.bound 9) .newest
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl rfl rfl rfl
    ?_ hZF ρ O names hp hz hInput
  intro K hK η O' _ _ _ hα U hU hpU ξ hξ
  obtain ⟨hw, hB, hR, hc, hTests, htL, hb, hSplit, hW, hS, ht, hSub⟩ :=
    (Syntax.splittingInput_semantics hK.1 η).mp hα
  have hcU := hU.upward _ _ hpU hc.1 (hc.2 _ (hU.proper _ hpU).1)
  obtain ⟨e, hv, he, hi⟩ := check_map_l O' hK hU hcU
  have heW : e (η.bound 11) = ξ.bound 2 := qval_unique_l (hv _ _ hW) (hξ 2)
  have heS : e (η.bound 4) = ξ.bound 0 := qval_unique_l (hv _ _ hS) (hξ 0)
  have htV : Qval_d K (η.bound 9) (η.bound 8) (η.bound 9) U (η.bound 3) (ξ.bound 1) := hξ 1
  let τ : Env K 2 := (⟨fun _ => η.bound 3, fun _ => η.bound 3⟩ : Env K 1).push (η.bound 2)
  let ζ : Env (extension_l K hK (η.bound 9) (η.bound 8) (η.bound 9) U) 2 :=
    (⟨fun _ => ξ.bound 1, fun _ => ξ.bound 1⟩ : Env _ 1).push (e (η.bound 11))
  have hSub' : Forces_d K (η.bound 9) (η.bound 8) (η.bound 9)
      (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2) τ (η.bound 0) :=
    (forces_env_l hK.1 _ ((Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩)
      _ τ (Fin.cases rfl (fun _ => rfl)) (η.bound 0)).mp hSub
  have hVal : Env_val_d hK τ ζ := by
    intro v
    cases v with
    | free _ => exact htV
    | bound i => exact Fin.cases (hv _ _ hW) (fun _ => htV) i
  have hTw : Internal.Subset (extension_l K hK (η.bound 9) (η.bound 8) (η.bound 9) U).mem
      (ξ.bound 1) (e (η.bound 11)) :=
    (Project.Formula.satisfies_subset_iff ζ (.bound 1) .newest).mp
      ((forcing_truth_l O' hK hU _ ((Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩)
        τ ζ hVal).mp ⟨η.bound 0, hpU, hSub'⟩)
  have hResult := name_splitting_in_extension hK O' hU hw hB hR hTests htL hb hSplit e hi he hv htV hTw
  apply (Syntax.splitsSetFormula_semantics (extension_ext_l O' hK hU) ξ (.bound 2) (.bound 1) .newest).mpr
  change SplitsSet (M := extension_l K hK (η.bound 9) (η.bound 8) (η.bound 9) U)
    (ξ.bound 2) (ξ.bound 1) (ξ.bound 0)
  rwa [heW, heS] at hResult

namespace Syntax
def splittingBody : Project.Formula 1 12 :=
  .imp (cond_order_m (.bound 9) (.bound 8) (.bound 9))
    (.imp (.mem .newest (.bound 9)) (.imp (Project.Formula.extensionalNe .newest (.bound 9))
      (.imp splittingInput splittingConclusion)))

theorem splittingBody_closed : splittingBody.FreeClosed := by
  simp -implicitDefEqProofs [splittingBody, Definitional.Formula.FreeClosed,
    splittingInput_closed, splittingConclusion_closed]

def splittingSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose splittingBody) (ObjectTheory.universalClose_closed _ splittingBody_closed)

theorem splittingBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 12) :
    Project.Formula.satisfies ρ splittingBody := by
  simp only [splittingBody, Project.Formula.satisfies_imp_iff, cond_order_sat_l hZF.1,
    Project.Formula.satisfies_mem_iff, Project.Formula.extensionalNe,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq hZF.1]
  exact fun O hp hz h => forces_splitting_from_tests hZF ρ O hp hz h
end Syntax

theorem derives_forced_splitting : Project.Derives SetTheory.ZF Syntax.splittingSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.splittingBody (Syntax.splittingBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

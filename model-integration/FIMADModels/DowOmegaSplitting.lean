import FIMADModels.DowSplittingForcing

/-! Preservation for countable families of ground-model forcing names.
An actual omega-splitting family supplies the common splitter of the internal
test family. The conclusion is a translated forcing formula for every input
name. Coding arbitrary extension countable families by such names is separate.
-/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def OmegaSplittingTests (w S : M.Domain) : Prop :=
  ∀ H, InternalCountable w H → (∀ X, M.mem X H → Internal.Subset M.mem X w) →
    ∃ b, M.mem b S ∧ Internal.Subset M.mem b w ∧ SplitsTests w b H

def SplitsNames (B R W L bs : M.Domain) : Prop :=
  ∀ t, M.mem t L → ∀ p, M.mem p B →
    Forces_d M B R B (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
      ((⟨fun _ => t, fun _ => t⟩ : Env M 1).push W) p →
    Forces_d M B R B (Syntax.splitsSetFormula (.bound 2) (.bound 1) .newest)
      (((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t).push bs) p

theorem preserves_countable_unbounded_names (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W L S : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hLc : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t ∧ ForcesUnboundedName B R W t)
    (hS : OmegaSplittingTests w S) :
    ∃ b bs, M.mem b S ∧ Internal.Subset M.mem b w ∧ Check_d M c b bs ∧ SplitsNames B R W L bs := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨H, hHc, hHw, hGood⟩ := countable_name_tests_exists hZFC hw O hB hR hc hTop hW hLc hNames
  obtain ⟨b, hbS, hbw, hSplit⟩ := hS H hHc hHw
  obtain ⟨bs, hbs, _, _⟩ := zf_check_l M hZF hc b
  refine ⟨b, bs, hbS, hbw, hbs, ?_⟩
  intro t htL p hp hSub
  let ρ : Env M 12 := (((((((((((⟨fun _ => w, fun _ => t⟩ : Env M 1).push A).push B).push R).push c).push L).push H).push b).push t).push W).push bs).push p
  have hSub' : Forces_d M B R B (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
      (⟨fun i => (Fin.cases (.bound 2) (fun _ => .bound 3) i : Project.Term 12).eval ρ, ρ.free⟩ : Env M 2) p :=
    (forces_env_l hZF.1 _ ((Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩)
      _ _ (Fin.cases rfl (fun _ => rfl)) p).mp hSub
  have hInput : Project.Formula.satisfies ρ Syntax.splittingInput :=
    (Syntax.splittingInput_semantics hZF.1 ρ).mpr
      ⟨hw, hB, hR, ⟨hc, hTop⟩, ⟨hHc, hHw, hGood⟩, htL, hbw, hSplit, hW, hbs, (hNames t htL).1, hSub'⟩
  have hpz : p ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  have h := (force_at_sat_l _ ρ Syntax.splittingArguments (.bound 9) (.bound 8) (.bound 9) .newest).mp
    (forces_splitting_from_tests hZF ρ O hp hpz hInput)
  exact (forces_env_l hZF.1 _ (Syntax.splitsSetFormula_freeClosed _ _ _ rfl rfl rfl)
    _ _ (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp h

namespace Syntax
def omegaSplittingTestsFormula {n} (w S : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.existsE (Internal.Syntax.InjectionFormula .newest (.bound 1) w.weaken.weaken))
    (.imp (.forallE (.imp (.mem .newest (.bound 1)) (Internal.Syntax.SubsetFormula .newest w.weaken.weaken)))
      (.existsE (.conj (.mem .newest S.weaken.weaken)
        (.conj (Internal.Syntax.SubsetFormula .newest w.weaken.weaken)
          (splitsTestsFormula w.weaken.weaken .newest (.bound 1)))))))

def splitsNamesFormula {n} (B R W L bs : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest L.weaken) (.forallE (.imp (.mem .newest B.weaken.weaken)
    (.imp (force_at_m (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
      (Fin.cases W.weaken.weaken (fun _ => .bound 1))
      B.weaken.weaken R.weaken.weaken B.weaken.weaken .newest)
      (force_at_m (splitsSetFormula (.bound 2) (.bound 1) .newest : Project.Formula 1 3)
        (Fin.cases bs.weaken.weaken (Fin.cases (.bound 1) (fun _ => W.weaken.weaken)))
        B.weaken.weaken R.weaken.weaken B.weaken.weaken .newest)))))

derive_free_closed omegaSplittingTestsFormula

@[simp] theorem splitsNamesFormula_freeClosed {n} (B R W L bs : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hW : W.freeSupport = [])
    (hL : L.freeSupport = []) (hbs : bs.freeSupport = []) : (splitsNamesFormula B R W L bs).FreeClosed := by
  simp only [splitsNamesFormula, Definitional.Formula.FreeClosed]
  refine ⟨⟨rfl, by simpa using hL⟩, ⟨rfl, by simpa using hB⟩, ?_, ?_⟩
  · apply force_at_closed_l
    · exact (Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩
    · exact Fin.cases (by simpa using hW) (fun _ => rfl)
    · simpa using hB
    · simpa using hR
    · simpa using hB
    · rfl
  · apply force_at_closed_l
    · exact splitsSetFormula_freeClosed _ _ _ rfl rfl rfl
    · exact Fin.cases (by simpa using hbs) (Fin.cases rfl (fun _ => by simpa using hW))
    · simpa using hB
    · simpa using hR
    · simpa using hB
    · rfl

theorem omegaSplittingTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w S : Project.Term n) : Project.Formula.satisfies ρ (omegaSplittingTestsFormula w S) ↔
      OmegaSplittingTests (w.eval ρ) (S.eval ρ) := by
  simp only [omegaSplittingTestsFormula, OmegaSplittingTests, InternalCountable,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff, Internal.Syntax.satisfies_InjectionFormula hE,
    Project.Formula.satisfies_mem_iff, Internal.Syntax.satisfies_SubsetFormula hE,
    Project.Formula.satisfies_conj_iff, splitsTestsFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem splitsNamesFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R W L bs : Project.Term n) : Project.Formula.satisfies ρ (splitsNamesFormula B R W L bs) ↔
      SplitsNames (B.eval ρ) (R.eval ρ) (W.eval ρ) (L.eval ρ) (bs.eval ρ) := by
  simp only [splitsNamesFormula, SplitsNames, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff, force_at_sat_l,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro _
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  apply imp_congr
  · apply forces_env_l hE _ ((Project.Formula.subset_freeClosed_iff _ _).mpr ⟨rfl, rfl⟩)
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · simp only [Fin.cases_zero, Definitional.Term.eval_weaken]
      rfl
    · rfl
  · apply forces_env_l hE _ (splitsSetFormula_freeClosed _ _ _ rfl rfl rfl)
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) i
    · simp only [Fin.cases_zero, Definitional.Term.eval_weaken]
      rfl
    · rfl
    · simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
      rfl

def omegaPreservationBody : Project.Formula 1 8 :=
  .imp (Project.Formula.isOmega (.bound 7))
    (.imp (carrierFormula (.bound 7) (.bound 6) (.bound 5))
      (.imp (orderFormula (.bound 5) (.bound 4))
        (.imp (cond_order_m (.bound 5) (.bound 4) (.bound 5))
          (.imp (topFormula (.bound 5) (.bound 4) (.bound 3))
            (.imp (check_m (.bound 3) (.bound 7) (.bound 2))
              (.imp (.existsE (Internal.Syntax.InjectionFormula .newest (.bound 2) (.bound 8)))
                (.imp (unboundedNameFamilyFormula (.bound 5) (.bound 4) (.bound 2) (.bound 1))
                  (.imp (omegaSplittingTestsFormula (.bound 7) .newest)
                    (.existsE (.existsE (.conj (.mem (.bound 1) (.bound 2))
                      (.conj (Internal.Syntax.SubsetFormula (.bound 1) (.bound 9))
                        (.conj (check_m (.bound 5) (.bound 1) .newest)
                          (splitsNamesFormula (.bound 7) (.bound 6) (.bound 4) (.bound 3) .newest))))))))))))))

theorem omegaPreservationBody_closed : omegaPreservationBody.FreeClosed := by
  simp -implicitDefEqProofs [omegaPreservationBody, Definitional.Formula.FreeClosed]

def omegaPreservationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose omegaPreservationBody)
  (ObjectTheory.universalClose_closed _ omegaPreservationBody_closed)

theorem omegaPreservationBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 8) :
    Project.Formula.satisfies ρ omegaPreservationBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [omegaPreservationBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    carrierFormula_semantics hZF.1, orderFormula_semantics hZF.1, cond_order_sat_l hZF.1,
    topFormula_semantics hZF.1, check_sat_l M hZF.1, Project.Formula.satisfies_exists_iff,
    Internal.Syntax.satisfies_InjectionFormula hZF.1, unboundedNameFamilyFormula_semantics hZF.1,
    omegaSplittingTestsFormula_semantics hZF.1, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Internal.Syntax.satisfies_SubsetFormula hZF.1,
    splitsNamesFormula_semantics hZF.1]
  intro hw hB hR O hc hW hLc hNames hS
  exact preserves_countable_unbounded_names hZFC hw O hB hR hc.1 hc.2 hW hLc hNames hS
end Syntax

theorem derives_preservation_for_countable_names : Project.Derives SetTheory.ZFC Syntax.omegaPreservationSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.omegaPreservationBody (Syntax.omegaPreservationBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

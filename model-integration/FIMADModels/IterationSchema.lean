import FIMADModels.Iteration

/-! An object-theory schema constructing the complete finite-support iteration.
The external index is an actual BinarySchema, whose parameters are universally
closed. Its totality/uniqueness and name-level CCC specifications occur in the
object sentence as hypotheses, not as added axioms. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace InfinitaryCombinatorics.Formalizations.FIMAD.Iteration
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal

@[simp] theorem nextFormula_freeClosed {n} (α B R e D V : Project.Term n)
    (hα : α.freeSupport = []) (hB : B.freeSupport = []) (hR : R.freeSupport = [])
    (he : e.freeSupport = []) (hD : D.freeSupport = []) (hV : V.freeSupport = []) :
    (nextFormula α B R e D V).FreeClosed := nextFormula_closed _ _ _ _ _ _ hα hB hR he hD hV

@[simp] theorem stagesCCCFormula_freeClosed {n} (ω F H : Project.Term n)
    (hω : ω.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = []) :
    (stagesCCCFormula ω F H).FreeClosed := stagesCCCFormula_closed _ _ _ hω hF hH

def ruleCall {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m)
    (δ F H e D V : Project.Term m) : Project.Formula 1 m :=
  binary_pred_m φ (Fin.cases e (Fin.cases H (Fin.cases F (Fin.cases δ es)))) D V

@[simp] theorem ruleCall_freeClosed {n m} (φ : BinarySchema (n+4))
    (es : Fin n → Project.Term m) (δ F H e D V : Project.Term m)
    (hes : ∀ i, (es i).freeSupport = []) (hδ : δ.freeSupport = [])
    (hF : F.freeSupport = []) (hH : H.freeSupport = []) (he : e.freeSupport = [])
    (hD : D.freeSupport = []) (hV : V.freeSupport = []) :
    (ruleCall φ es δ F H e D V).FreeClosed :=
  binary_pred_closed_l _ _ _ _ (Fin.cases he (Fin.cases hH (Fin.cases hF (Fin.cases hδ hes)))) hD hV

def extendFormula {m} (ω δ F H e D V : Project.Term m) : Project.Formula 1 m :=
  .conj (row_stage_m δ D V e)
    (.conj (.forallE (.forallE (.forallE
      (.imp (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
        (.imp (entry_m (.bound 2) .newest H.weaken.weaken.weaken)
          (row_link_m (.bound 2) (.bound 1) .newest D.weaken.weaken.weaken V.weaken.weaken.weaken))))))
      (.forallE (.imp (.mem .newest D.weaken) (row_supp_m kpair_convention_l false ω.weaken .newest))))

derive_free_closed extendFormula

def ruleFormula {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m)
    (ω : Project.Term m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE
    (.imp (row_system_m (.bound 3) (.bound 2) (.bound 1) .newest)
      (.imp (row_system_supp_m false ω.weaken.weaken.weaken.weaken (.bound 2))
        (.imp (.existsE (Project.Formula.isSuccessor (.bound 4) .newest))
          (.existsE (.existsE (.conj
            (ruleCall φ (fun i => (es i).weaken.weaken.weaken.weaken.weaken.weaken)
              (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
            (.conj (extendFormula ω.weaken.weaken.weaken.weaken.weaken.weaken
              (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
              (.forallE (.forallE (.imp
                (ruleCall φ (fun i => (es i).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken)
                  (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)
                (.conj (Project.Formula.extensionalEq (.bound 1) (.bound 3))
                  (Project.Formula.extensionalEq .newest (.bound 2))))))))))))))))

@[simp] theorem ruleFormula_freeClosed {n m} (φ : BinarySchema (n+4))
    (es : Fin n → Project.Term m) (ω : Project.Term m)
    (hes : ∀ i, (es i).freeSupport = []) (hω : ω.freeSupport = []) :
    (ruleFormula φ es ω).FreeClosed := by
  simp -implicitDefEqProofs [ruleFormula, Definitional.Formula.FreeClosed, *]

def cccRuleFormula {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (row_system_m (.bound 5) (.bound 4) (.bound 3) (.bound 2))
      (.imp (.existsE (Project.Formula.isSuccessor (.bound 6) .newest))
        (.imp (ruleCall φ (fun i => (es i).weaken.weaken.weaken.weaken.weaken.weaken)
          (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
          (.existsE (.existsE (.existsE
            (.conj (Project.Formula.isSuccessor (.bound 8) (.bound 2))
              (.conj (entry_m (.bound 2) (.bound 1) (.bound 7))
                (.conj (entry_m (.bound 2) .newest (.bound 6))
                  (nextFormula (.bound 2) (.bound 1) .newest (.bound 5) (.bound 4) (.bound 3))))))))))))))))

@[simp] theorem cccRuleFormula_freeClosed {n m} (φ : BinarySchema (n+4))
    (es : Fin n → Project.Term m) (hes : ∀ i, (es i).freeSupport = []) :
    (cccRuleFormula φ es).FreeClosed := by
  simp -implicitDefEqProofs [cccRuleFormula, Definitional.Formula.FreeClosed, *]

def iterationFormula {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m)
    (ω e γ F H : Project.Term m) : Project.Formula 1 m :=
  binary_pred_m (row_iteration_s φ false) (Fin.cases γ (Fin.cases e (Fin.cases ω es))) F H

@[simp] theorem iterationFormula_freeClosed {n m} (φ : BinarySchema (n+4))
    (es : Fin n → Project.Term m) (ω e γ F H : Project.Term m)
    (hes : ∀ i, (es i).freeSupport = []) (hω : ω.freeSupport = []) (he : e.freeSupport = [])
    (hγ : γ.freeSupport = []) (hF : F.freeSupport = []) (hH : H.freeSupport = []) :
    (iterationFormula φ es ω e γ F H).FreeClosed :=
  binary_pred_closed_l _ _ _ _ (Fin.cases hγ (Fin.cases he (Fin.cases hω hes))) hF hH

universe u
variable {M : SetTheory.Structure.{u}}

@[simp] theorem evalConsEnv {n m} (ρ : Env M m) (a : Project.Term m) (es : Fin n → Project.Term m) :
    (⟨fun i => (Fin.cases a es i : Project.Term m).eval ρ, ρ.free⟩ : Env M (n+1)) =
      (⟨fun i => (es i).eval ρ, ρ.free⟩ : Env M n).push (a.eval ρ) := by
  rw [Env.mk.injEq]
  exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
theorem ruleCall_semantics {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m)
    (ρ : Env M m) (δ F H e D V : Project.Term m) :
    Project.Formula.satisfies ρ (ruleCall φ es δ F H e D V) ↔
      φ.denote (row_rule_env_l ⟨fun i => (es i).eval ρ, ρ.free⟩
        (δ.eval ρ) (F.eval ρ) (H.eval ρ) (e.eval ρ)) (D.eval ρ) (V.eval ρ) := by
  rw [ruleCall, binary_pred_sat_l, evalConsEnv, evalConsEnv, evalConsEnv, evalConsEnv]
  rfl

theorem extendFormula_semantics (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {m} (ρ : Env M m) (ω δ F H e D V : Project.Term m) :
    Project.Formula.satisfies ρ (extendFormula ω δ F H e D V) ↔
      Row_extend_d I false (ω.eval ρ) (δ.eval ρ) (F.eval ρ) (H.eval ρ) (e.eval ρ) (D.eval ρ) (V.eval ρ) := by
  simp only [extendFormula, Row_extend_d, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, row_stage_sat_l hE, row_link_sat_l I hE,
    entry_sat_l M hE, row_supp_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

theorem ruleFormula_semantics (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m) (ρ : Env M m) (ω : Project.Term m) :
    Project.Formula.satisfies ρ (ruleFormula φ es ω) ↔
      Row_rule_d I false (ω.eval ρ) φ ⟨fun i => (es i).eval ρ, ρ.free⟩ := by
  simp only [ruleFormula, Row_rule_d, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isSuccessor_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, row_system_sat_l I hE,
    row_system_supp_sat_l I hE, ruleCall_semantics, extendFormula_semantics I hE,
    Definitional.Term.eval_weaken]
  rfl

theorem cccRuleFormula_semantics (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m) (ρ : Env M m) :
    Project.Formula.satisfies ρ (cccRuleFormula φ es) ↔
      Row_ccc_rule_d I φ ⟨fun i => (es i).eval ρ, ρ.free⟩ := by
  simp only [cccRuleFormula, Row_ccc_rule_d, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_isSuccessor_iff,
    row_system_sat_l I hE, entry_sat_l M hE, ruleCall_semantics,
    nextFormula_semantics hE, Definitional.Term.eval_weaken]
  rfl

theorem iterationFormula_semantics (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {n m} (φ : BinarySchema (n+4)) (es : Fin n → Project.Term m) (ρ : Env M m) (ω e γ F H : Project.Term m) :
    Project.Formula.satisfies ρ (iterationFormula φ es ω e γ F H) ↔
      Row_iteration_d I false (ω.eval ρ) (e.eval ρ) φ
        ⟨fun i => (es i).eval ρ, ρ.free⟩ (γ.eval ρ) (F.eval ρ) (H.eval ρ) := by
  rw [iterationFormula, binary_pred_sat_l, evalConsEnv, evalConsEnv, evalConsEnv]
  exact row_iteration_denote_l I hE φ ⟨fun i => (es i).eval ρ, ρ.free⟩ false _ _ _ _ _

/-- The original successor formula is the external index of this theorem schema. -/
def iterationExistsBody {n} (φ : BinarySchema (n+4)) : Project.Formula 1 (n+3) :=
  let es : Fin n → Project.Term (n+3) := fun i => .bound ⟨i.val+3, by omega⟩
  .imp (Project.Formula.isOmega (.bound 2))
    (.imp (Project.Formula.isEmpty (.bound 1))
      (.imp (Project.Formula.isOrdinal (.bound 0))
        (.imp (ruleFormula φ es (.bound 2))
          (.imp (cccRuleFormula φ es)
            (.existsE (.existsE (.conj
              (iterationFormula φ (fun i => (es i).weaken.weaken) (Project.Term.bound 2).weaken.weaken (Project.Term.bound 1).weaken.weaken (Project.Term.bound 0).weaken.weaken Project.Term.newest.weaken .newest)
              (stagesCCCFormula (Project.Term.bound 2).weaken.weaken Project.Term.newest.weaken .newest))))))))

theorem iterationExistsBody_closed {n} (φ : BinarySchema (n+4)) :
    (iterationExistsBody φ).FreeClosed := by
  simp -implicitDefEqProofs [iterationExistsBody, Definitional.Formula.FreeClosed]

def iterationExistsSentence {n} (φ : BinarySchema (n+4)) : Project.Sentence :=
  Project.Sentence.ofFormula (ObjectTheory.universalClose (iterationExistsBody φ))
    (ObjectTheory.universalClose_closed _ (iterationExistsBody_closed φ))

/-- The native semantic step for the open body, checked separately from closure. -/
theorem iterationExistsBody_valid {n} (φ : BinarySchema (n+4)) (M : SetTheory.Structure.{u})
    (hZFC : M.Models SetTheory.ZFC) (ρ : Env M (n+3)) :
    Project.Formula.satisfies ρ (iterationExistsBody φ) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  simp only [iterationExistsBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isOrdinal_iff, ruleFormula_semantics I hZF.1,
    cccRuleFormula_semantics I hZF.1, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, iterationFormula_semantics I hZF.1,
    stagesCCCFormula_semantics I hZF.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  intro hω he hγ hRule hC
  exact row_iteration_ccc_exists_l (n := n) (φ := φ)
    (ρ := ⟨fun i => (Project.Term.bound ⟨i.val+3, by omega⟩).eval ρ, ρ.free⟩)
    hZFC hω he hγ hRule hC

/-- Universal closure uses all model environments, without standardness. -/
theorem native_iteration_exists {n} (φ : BinarySchema (n+4)) (M : SetTheory.Structure.{u})
    (hZFC : M.Models SetTheory.ZFC) : M.SatisfiesSentence (iterationExistsSentence φ) := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid (iterationExistsBody φ)
    (iterationExistsBody_valid φ M hZFC)
/-- Every externally indexed instance is an original ZFC derivation. -/
theorem derives_iteration_exists {n} (φ : BinarySchema (n+4)) :
    Project.Derives SetTheory.ZFC (iterationExistsSentence φ) :=
  ObjectTheory.derives_of_native_zfc_models (iterationExistsSentence φ)
    (native_iteration_exists φ)
end InfinitaryCombinatorics.Formalizations.FIMAD.Iteration

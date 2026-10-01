import FIMADModels.CountableRealEnumeration

/-! An internal countable set of names for the values of an omega-function
name. The witnesses come from the original maximum principle and model
collection, with one name for each internal natural number. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def functionValueSchema : UnarySchema 2 where
  body := Internal.Syntax.ValueFormula (.bound 2) (.bound 1) .newest
  freeClosed := by simp -implicitDefEqProofs

def functionValueExistsSchema : UnarySchema 1 where
  body := .existsE functionValueSchema.body
  freeClosed := by simpa only [Definitional.Formula.FreeClosed] using functionValueSchema.freeClosed

def functionValueExistsFormula {n} (Q k : Project.Term n) : Project.Formula 1 n :=
  pred_m functionValueExistsSchema (fun _ => Q) k

@[simp] theorem functionValueExistsFormula_closed {n} (Q k : Project.Term n)
    (hQ : Q.freeSupport = []) (hk : k.freeSupport = []) :
    (functionValueExistsFormula Q k).FreeClosed := by
  simp -implicitDefEqProofs [functionValueExistsFormula, hQ, hk]

theorem functionValueExistsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (Q k : Project.Term n) : Project.Formula.satisfies ρ (functionValueExistsFormula Q k) ↔
      ∃ t, Internal.Value M.mem (Q.eval ρ) (k.eval ρ) t := by
  rw [functionValueExistsFormula, pred_sat_l]
  simp only [UnarySchema.denote, functionValueExistsSchema, Project.Formula.satisfies_exists_iff,
    functionValueSchema, Internal.Syntax.satisfies_ValueFormula hE]
  rfl

def functionTotalBody : Project.Formula 1 2 :=
  .imp (Internal.Syntax.FunctionOnFormula .newest (.bound 1))
    (.forallE (.imp (.mem .newest (.bound 2)) (functionValueExistsFormula (.bound 1) .newest)))

theorem functionTotalBody_closed : functionTotalBody.FreeClosed := by
  simp -implicitDefEqProofs [functionTotalBody, Definitional.Formula.FreeClosed]

theorem functionTotalBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 2) :
    Project.Formula.satisfies ρ functionTotalBody := by
  simp only [functionTotalBody, Project.Formula.satisfies_imp_iff,
    Internal.Syntax.satisfies_FunctionOnFormula hZF.1, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff, functionValueExistsFormula_semantics hZF.1]
  intro hQ n hn
  obtain ⟨t, ht, _⟩ := hQ.2 n hn
  exact ⟨t, ht⟩

def forceFunctionValueFormula {n} (B R z Q k t p : Project.Term n) : Project.Formula 1 n :=
  force_at_m functionValueSchema.body (Fin.cases t (Fin.cases k (fun _ => Q))) B R z p

@[simp] theorem forceFunctionValueFormula_closed {n} (B R z Q k t p : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hQ : Q.freeSupport = []) (hk : k.freeSupport = []) (ht : t.freeSupport = [])
    (hp : p.freeSupport = []) : (forceFunctionValueFormula B R z Q k t p).FreeClosed := by
  unfold forceFunctionValueFormula
  apply force_at_closed_l
  · exact functionValueSchema.freeClosed
  · exact Fin.cases ht (Fin.cases hk (fun _ => hQ))
  · exact hB
  · exact hR
  · exact hz
  · exact hp

def forceFunctionValueExistsFormula {n} (B R z Q k p : Project.Term n) : Project.Formula 1 n :=
  force_at_m functionValueExistsSchema.body (Fin.cases k (fun _ => Q)) B R z p

@[simp] theorem forceFunctionValueExistsFormula_closed {n} (B R z Q k p : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hQ : Q.freeSupport = []) (hk : k.freeSupport = []) (hp : p.freeSupport = []) :
    (forceFunctionValueExistsFormula B R z Q k p).FreeClosed := by
  unfold forceFunctionValueExistsFormula
  apply force_at_closed_l
  · exact functionValueExistsSchema.freeClosed
  · exact Fin.cases hk (fun _ => hQ)
  · exact hB
  · exact hR
  · exact hz
  · exact hp

def valueMaximumFormula {n} (B R z Q c k t : Project.Term n) : Project.Formula 1 n :=
  .conj (name_m B t) (.existsE (.conj (check_m c.weaken k.weaken .newest)
    (.forallE (.imp (.conj (.mem .newest B.weaken.weaken)
      (.neg (Project.Formula.extensionalEq .newest z.weaken.weaken)))
      (.imp (forceFunctionValueExistsFormula B.weaken.weaken R.weaken.weaken z.weaken.weaken
        Q.weaken.weaken (.bound 1) .newest)
        (forceFunctionValueFormula B.weaken.weaken R.weaken.weaken z.weaken.weaken
          Q.weaken.weaken (.bound 1) t.weaken.weaken .newest))))))

derive_free_closed valueMaximumFormula
end Syntax

def ValueMaximum (B R z Q c k t : M.Domain) : Prop :=
  Name_d M B t ∧ ∃ s, Check_d M c k s ∧ ∀ p, M.mem p B → p ≠ z →
    Forces_d M B R z Syntax.functionValueExistsSchema.body
      ((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push s) p →
    Forces_d M B R z Syntax.functionValueSchema.body
      (((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push s).push t) p

namespace Syntax
theorem valueMaximumFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R z Q c k t : Project.Term n) :
    Project.Formula.satisfies ρ (valueMaximumFormula B R z Q c k t) ↔
      ValueMaximum (B.eval ρ) (R.eval ρ) (z.eval ρ) (Q.eval ρ) (c.eval ρ) (k.eval ρ) (t.eval ρ) := by
  simp only [valueMaximumFormula, ValueMaximum, Project.Formula.satisfies_conj_iff,
    name_sat_l M hE, Project.Formula.satisfies_exists_iff, check_sat_l M hE,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, forceFunctionValueExistsFormula,
    forceFunctionValueFormula, force_at_sat_l, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  apply and_congr_right
  intro _
  apply exists_congr
  intro s
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  rw [and_imp]
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  apply imp_congr
  · apply forces_env_l hE functionValueExistsSchema.body functionValueExistsSchema.freeClosed _
      ((⟨fun _ => Q.eval ρ, fun _ => Q.eval ρ⟩ : Env M 1).push s)
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · rfl
    · simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
      rfl
  · apply forces_env_l hE functionValueSchema.body functionValueSchema.freeClosed _
      (((⟨fun _ => Q.eval ρ, fun _ => Q.eval ρ⟩ : Env M 1).push s).push (t.eval ρ))
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => ?_)) i
    · simp only [Fin.cases_zero, Definitional.Term.eval_weaken]
      rfl
    · rfl
    · simp only [Fin.cases_succ, Definitional.Term.eval_weaken]
      rfl
end Syntax

theorem value_maximum_exists (hZFC : M.Models SetTheory.ZFC)
    {B R z Q c : M.Domain} (O : Cond_order_d M B R z) (hQ : Name_d M B Q)
    (hc : M.mem c B) (k : M.Domain) : ∃ t, ValueMaximum B R z Q c k t := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨s, hs, _, _⟩ := zf_check_l M hZF hc k
  have hsN := check_name_l M (check_range_l M hZF) hc hs
  let ρ : Env M 2 := (⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push s
  obtain ⟨t, ht, _, hMax⟩ := maximum_l O hZFC Syntax.functionValueSchema ρ
    (Fin.cases hsN (fun _ => hQ))
  exact ⟨t, ht, s, hs, fun p hp hz h => (hMax p hp hz).mp h⟩

theorem countable_function_value_names (hZFC : M.Models SetTheory.ZFC)
    {w B R z Q c : M.Domain} (O : Cond_order_d M B R z) (hQ : Name_d M B Q)
    (hc : M.mem c B) :
    ∃ G L, InternalCountable w L ∧
      (∀ t, M.mem t L ↔ ∃ k, M.mem k w ∧ Entry_d M k t G) ∧
      (∀ k, M.mem k w → ∃ t, M.mem t L ∧ Entry_d M k t G) ∧
      (∀ k t, Entry_d M k t G → ValueMaximum B R z Q c k t) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 5 := ((((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push Q).push c
  let φ : BinarySchema 5 := {
    body := Syntax.valueMaximumFormula (.bound 6) (.bound 5)
      (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ k t : φ.denote ρ k t ↔ ValueMaximum B R z Q c k t :=
    Syntax.valueMaximumFormula_semantics hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨Y, G, hG, he⟩ := ZFC.collect_choice_l I hZFC φ ρ w (fun k _ => by
    obtain ⟨t, ht⟩ := value_maximum_exists hZFC O hQ hc k
    exact ⟨t, (hφ k t).mpr ht⟩)
  obtain ⟨j, hj⟩ := ZF.exists_inclusionInjection hZF I (source := w) (target := w) (fun _ h => h)
  have hww : InternalCountable w w := ⟨j, (ForcingFinite.injection_correct hZF j w w).mpr hj⟩
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : BinarySchema 1 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hψ k t : ψ.denote η k t ↔ Entry_d M k t G := entry_sat_l M hZF.1 _ _ _ _
  obtain ⟨L, hL, hLc⟩ := countable_test_image hZFC ψ η hww (by
    intro k hk
    obtain ⟨t, _, hkt⟩ := hG.2.2 k hk
    exact ⟨t, (hψ k t).mpr hkt⟩) (by
      intro k _ t t' ht ht'
      exact hG.1.2 k t t' ((hψ k t).mp ht) ((hψ k t').mp ht'))
  have hL' t : M.mem t L ↔ ∃ k, M.mem k w ∧ Entry_d M k t G := by
    rw [hL]
    exact exists_congr fun k => and_congr_right fun _ => hψ k t
  refine ⟨G, L, hLc, hL', ?_, fun k t hkt => (hφ k t).mp (he k t hkt)⟩
  intro k hk
  obtain ⟨t, _, hkt⟩ := hG.2.2 k hk
  exact ⟨t, (hL' t).mpr ⟨k, hk, hkt⟩, hkt⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

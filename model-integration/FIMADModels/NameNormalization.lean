import FIMADModels.DowInfiniteNames
import YesMetaZFC.Model.Forcing.Internal.Maximum.Basic

/-! Global infinite-real names obtained by the original-formula maximum
principle. The normalized name agrees with the input wherever that input is
forced to be an infinite subset of omega. No external well-foundedness or
countable ground-model enumeration is used. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def infiniteRealSchema : UnarySchema 1 where
  body := .conj (Internal.Syntax.SubsetFormula .newest (.bound 1))
    (Internal.Syntax.InfiniteFormula (.bound 1) .newest)
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

def infiniteRealFormula {n} (w t : Project.Term n) : Project.Formula 1 n :=
  pred_m infiniteRealSchema (fun _ => w) t

@[simp] theorem infiniteRealFormula_closed {n} (w t : Project.Term n)
    (hw : w.freeSupport = []) (ht : t.freeSupport = []) :
    (infiniteRealFormula w t).FreeClosed := by
  simp -implicitDefEqProofs [infiniteRealFormula, hw, ht]

theorem infiniteRealSchema_semantics (hE : Extensional M) (ρ : Env M 1) (t : M.Domain) :
    infiniteRealSchema.denote ρ t ↔
      Internal.Subset M.mem t (ρ.bound 0) ∧ Internal.Infinite M.mem (ρ.bound 0) t := by
  simp only [UnarySchema.denote, infiniteRealSchema, Project.Formula.satisfies_conj_iff,
    Internal.Syntax.satisfies_SubsetFormula hE, Internal.Syntax.satisfies_InfiniteFormula hE]
  rfl

theorem infiniteRealFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w t : Project.Term n) : Project.Formula.satisfies ρ (infiniteRealFormula w t) ↔
      Internal.Subset M.mem (t.eval ρ) (w.eval ρ) ∧
        Internal.Infinite M.mem (w.eval ρ) (t.eval ρ) := by
  rw [infiniteRealFormula, pred_sat_l, infiniteRealSchema_semantics hE]

def infiniteNormalizerSchema : UnarySchema 2 where
  body := .conj (infiniteRealFormula (.bound 2) .newest)
    (.imp (infiniteRealFormula (.bound 2) (.bound 1))
      (Project.Formula.extensionalEq .newest (.bound 1)))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

def infiniteNormalizerExistenceBody : Project.Formula 1 2 :=
  .imp (Project.Formula.isOmega (.bound 1)) (.existsE infiniteNormalizerSchema.body)

theorem infiniteNormalizerExistenceBody_closed : infiniteNormalizerExistenceBody.FreeClosed := by
  simp -implicitDefEqProofs [infiniteNormalizerExistenceBody, Definitional.Formula.FreeClosed]

theorem infiniteNormalizerExistenceBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 2) :
    Project.Formula.satisfies ρ infiniteNormalizerExistenceBody := by
  classical
  simp only [infiniteNormalizerExistenceBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    infiniteNormalizerSchema, Project.Formula.satisfies_conj_iff,
    infiniteRealFormula_semantics hZF.1, Project.Formula.satisfies_extensionalEq_iff_eq hZF.1]
  intro hw
  by_cases ht : Internal.Subset M.mem (ρ.bound 0) (ρ.bound 1) ∧
      Internal.Infinite M.mem (ρ.bound 1) (ρ.bound 0)
  · exact ⟨ρ.bound 0, ht, fun _ => rfl⟩
  · have hi : Internal.Infinite M.mem (ρ.bound 1) (ρ.bound 1) :=
      (Internal.infinite_iff_unbounded hZF
        ((Internal.omega_native_iff hZF.1 _).mpr hw) (fun _ h => h)).mpr
        (fun n hn => ⟨n, hn, Or.inr rfl, hn⟩)
    exact ⟨ρ.bound 1, ⟨fun _ h => h, hi⟩, fun h => False.elim (ht h)⟩
end Syntax

def ForcesInfiniteReal (B R z W t p : M.Domain) : Prop :=
  Forces_d M B R z Syntax.infiniteRealSchema.body
    ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p

theorem infinite_name_normalization (hZFC : M.Models SetTheory.ZFC)
    {B R z W t : M.Domain} (O : Cond_order_d M B R z)
    (hW : Name_d M B W) (ht : Name_d M B t)
    (hOmega : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z
      (Project.Formula.isOmega .newest : Project.Formula 1 1)
      (⟨fun _ => W, fun _ => W⟩ : Env M 1) p) :
    ∃ v, Name_d M B v ∧ ∀ p, M.mem p B → p ≠ z →
      ForcesInfiniteReal B R z W v p ∧
        (ForcesInfiniteReal B R z W t p → Eq_force_d M B R z p v t) := by
  let hZF := ZFC.models_zf_l hZFC
  let ρ : Env M 2 := (⟨fun _ => W, fun _ => t⟩ : Env M 1).push t
  have hρ : ∀ a : Project.Term 2, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact ht
    | bound i => exact Fin.cases ht (fun _ => hW) i
  obtain ⟨v, hv, _, hMax⟩ := maximum_l O hZFC Syntax.infiniteNormalizerSchema ρ
    (fun i => hρ (.bound i))
  have hξ : ∀ a : Project.Term 3, Name_d M B (a.eval (ρ.push v)) := by
    intro a
    cases a with
    | free _ => exact ht
    | bound i => exact Fin.cases hv (fun i => hρ (.bound i)) i
  refine ⟨v, hv, fun p hp hz => ?_⟩
  have hOmega' : Forces_d M B R z (Project.Formula.isOmega (.bound 1)) ρ p := by
    have hb : (Project.Formula.isOmega .newest : Project.Formula 1 1).bind
        (fun _ : Fin 1 => (.bound 1 : Project.Term 2)) = Project.Formula.isOmega (.bound 1 : Project.Term 2) := by
      simp [Project.Formula.isOmega, Project.Formula.isInductive, Project.Formula.isEmpty,
        Project.Formula.isSuccessor, Project.Formula.forallMem, Project.Formula.extensionalEq,
        Project.Formula.subset, Definitional.Formula.bind, Definitional.Term.bind,
        Definitional.Term.liftSubstitution, Definitional.Term.newest, Definitional.Term.weaken,
        Definitional.Term.rename, Definitional.TermVector.bind, Project.Formula.pairArguments,
        Fin.cases, Fin.induction, Fin.induction.go]
    rw [← hb, forces_bind_l hZF.1]
    exact (forces_env_l hZF.1 _ (Project.Formula.isOmega_freeClosed _ rfl)
      (⟨fun _ => W, fun _ => W⟩ : Env M 1)
      (Definitional.Env.substitute ρ (fun _ : Fin 1 => (.bound 1 : Project.Term 2)))
      (fun _ => rfl) p).mp (hOmega p hp hz)
  have hValid := forces_zf_valid_l O hZF Syntax.infiniteNormalizerExistenceBody
    Syntax.infiniteNormalizerExistenceBody_closed
    (fun _ hN η => Syntax.infiniteNormalizerExistenceBody_valid hN η) ρ
    (fun i => hρ (.bound i)) hp hz
  have hExists := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1
    (forces_regular_l O hZF _ ρ hρ) hp hz hValid hOmega'
  obtain ⟨hGood, hImp⟩ := (forces_conj_l _ _ (ρ.push v) p).mp ((hMax p hp hz).mp hExists)
  have hGood' := (forces_pred_l hZF.1 Syntax.infiniteRealSchema (ρ.push v)
    (fun _ => (.bound 2 : Project.Term 3)) .newest p).mp hGood
  have hg : ForcesInfiniteReal B R z W v p :=
    (forces_env_l hZF.1 _ Syntax.infiniteRealSchema.freeClosed _ _
      (Fin.cases rfl (fun _ => rfl)) p).mp hGood'
  refine ⟨hg, fun hLocal => ?_⟩
  have hLocal' : Forces_d M B R z (Syntax.infiniteRealFormula (.bound 2) (.bound 1)) (ρ.push v) p := by
    rw [Syntax.infiniteRealFormula, forces_pred_l hZF.1]
    exact (forces_env_l hZF.1 _ Syntax.infiniteRealSchema.freeClosed
      ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) _
      (Fin.cases rfl (fun _ => rfl)) p).mp hLocal
  have he := forces_mp_l hZF.1 (forces_regular_l O hZF _ (ρ.push v) hξ).1
    (forces_regular_l O hZF _ (ρ.push v) hξ) hp hz hImp hLocal'
  exact (code_eq_l M hZF.1 B R z .newest (.bound 1) (ρ.push v) p).mp he

theorem derives_infinite_normalizer_existence : Project.Derives SetTheory.ZF
    (Project.Sentence.ofFormula (ObjectTheory.universalClose Syntax.infiniteNormalizerExistenceBody)
      (ObjectTheory.universalClose_closed _ Syntax.infiniteNormalizerExistenceBody_closed)) := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid _ (Syntax.infiniteNormalizerExistenceBody_valid hZF)

namespace Syntax
def forceInfiniteRealFormula {n} (B R z W t p : Project.Term n) : Project.Formula 1 n :=
  force_at_m infiniteRealSchema.body (Fin.cases t (fun _ => W)) B R z p

@[simp] theorem forceInfiniteRealFormula_closed {n} (B R z W t p : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hW : W.freeSupport = []) (ht : t.freeSupport = []) (hp : p.freeSupport = []) :
    (forceInfiniteRealFormula B R z W t p).FreeClosed := by
  unfold forceInfiniteRealFormula
  apply force_at_closed_l
  · exact infiniteRealSchema.freeClosed
  · exact Fin.cases ht (fun _ => hW)
  · exact hB
  · exact hR
  · exact hz
  · exact hp

theorem forceInfiniteRealFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R z W t p : Project.Term n) :
    Project.Formula.satisfies ρ (forceInfiniteRealFormula B R z W t p) ↔
      ForcesInfiniteReal (B.eval ρ) (R.eval ρ) (z.eval ρ) (W.eval ρ) (t.eval ρ) (p.eval ρ) := by
  rw [forceInfiniteRealFormula, force_at_sat_l]
  exact forces_env_l hE _ infiniteRealSchema.freeClosed _ _ (Fin.cases rfl (fun _ => rfl)) _

def forceOmegaFormula {n} (B R z W p : Project.Term n) : Project.Formula 1 n :=
  force_at_m (Project.Formula.isOmega .newest : Project.Formula 1 1) (fun _ => W) B R z p

@[simp] theorem forceOmegaFormula_closed {n} (B R z W p : Project.Term n)
    (hB : B.freeSupport = []) (hR : R.freeSupport = []) (hz : z.freeSupport = [])
    (hW : W.freeSupport = []) (hp : p.freeSupport = []) :
    (forceOmegaFormula B R z W p).FreeClosed := by
  exact force_at_closed_l (Project.Formula.isOmega .newest : Project.Formula 1 1)
    (fun _ => W) B R z p (Project.Formula.isOmega_freeClosed .newest rfl)
    (fun _ => hW) hB hR hz hp

theorem forceOmegaFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R z W p : Project.Term n) :
    Project.Formula.satisfies ρ (forceOmegaFormula B R z W p) ↔
      Forces_d M (B.eval ρ) (R.eval ρ) (z.eval ρ)
        (Project.Formula.isOmega .newest : Project.Formula 1 1)
        (⟨fun _ => W.eval ρ, fun _ => W.eval ρ⟩ : Env M 1) (p.eval ρ) := by
  rw [forceOmegaFormula, force_at_sat_l]
  exact forces_env_l hE (Project.Formula.isOmega .newest : Project.Formula 1 1)
    (Project.Formula.isOmega_freeClosed .newest rfl)
    (⟨fun _ => W.eval ρ, ρ.free⟩ : Env M 1)
    (⟨fun _ => W.eval ρ, fun _ => W.eval ρ⟩ : Env M 1) (fun _ => rfl) (p.eval ρ)

def infiniteNameNormalizationBody : Project.Formula 1 5 :=
  .imp (cond_order_m (.bound 4) (.bound 3) (.bound 2))
    (.imp (name_m (.bound 4) (.bound 1))
      (.imp (name_m (.bound 4) .newest)
        (.imp (.forallE (.imp (.conj (.mem .newest (.bound 5))
          (.neg (Project.Formula.extensionalEq .newest (.bound 3))))
          (forceOmegaFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest)))
          (.existsE (.conj (name_m (.bound 5) .newest)
            (.forallE (.imp (.conj (.mem .newest (.bound 6))
              (.neg (Project.Formula.extensionalEq .newest (.bound 4))))
              (.conj (forceInfiniteRealFormula (.bound 6) (.bound 5) (.bound 4)
                (.bound 3) (.bound 1) .newest)
                (.imp (forceInfiniteRealFormula (.bound 6) (.bound 5) (.bound 4)
                  (.bound 3) (.bound 2) .newest)
                  (eq_force_m (.bound 6) (.bound 5) (.bound 4) .newest (.bound 1) (.bound 2)))))))))))

theorem infiniteNameNormalizationBody_closed : infiniteNameNormalizationBody.FreeClosed := by
  simp -implicitDefEqProofs [infiniteNameNormalizationBody, Definitional.Formula.FreeClosed]

def infiniteNameNormalizationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose infiniteNameNormalizationBody)
  (ObjectTheory.universalClose_closed _ infiniteNameNormalizationBody_closed)

theorem infiniteNameNormalizationBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 5) :
    Project.Formula.satisfies ρ infiniteNameNormalizationBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [infiniteNameNormalizationBody, Project.Formula.satisfies_imp_iff,
    cond_order_sat_l hZF.1, name_sat_l M hZF.1, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq hZF.1,
    forceOmegaFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
    forceInfiniteRealFormula_semantics hZF.1, eq_force_sat_l M hZF.1]
  intro O hW ht hOmega
  obtain ⟨v, hv, h⟩ := infinite_name_normalization hZFC O hW ht (fun p hp hz => hOmega p ⟨hp, hz⟩)
  exact ⟨v, hv, fun p ⟨hp, hz⟩ => h p hp hz⟩
end Syntax

theorem derives_infinite_name_normalization : Project.Derives SetTheory.ZFC Syntax.infiniteNameNormalizationSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid _ (Syntax.infiniteNameNormalizationBody_valid hZFC)

def NormalizesInfiniteName (B R z W t v : M.Domain) : Prop :=
  Name_d M B v ∧ ∀ p, M.mem p B → p ≠ z →
    ForcesInfiniteReal B R z W v p ∧
      (ForcesInfiniteReal B R z W t p → Eq_force_d M B R z p v t)

namespace Syntax
def normalizesInfiniteNameFormula {n} (B R z W t v : Project.Term n) : Project.Formula 1 n :=
  .conj (name_m B v)
    (.forallE (.imp (.conj (.mem .newest B.weaken)
      (.neg (Project.Formula.extensionalEq .newest z.weaken)))
      (.conj (forceInfiniteRealFormula B.weaken R.weaken z.weaken W.weaken v.weaken .newest)
        (.imp (forceInfiniteRealFormula B.weaken R.weaken z.weaken W.weaken t.weaken .newest)
          (eq_force_m B.weaken R.weaken z.weaken .newest v.weaken t.weaken)))))

derive_free_closed normalizesInfiniteNameFormula

theorem normalizesInfiniteNameFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R z W t v : Project.Term n) :
    Project.Formula.satisfies ρ (normalizesInfiniteNameFormula B R z W t v) ↔
      NormalizesInfiniteName (B.eval ρ) (R.eval ρ) (z.eval ρ) (W.eval ρ) (t.eval ρ) (v.eval ρ) := by
  simp only [normalizesInfiniteNameFormula, NormalizesInfiniteName,
    Project.Formula.satisfies_conj_iff, name_sat_l M hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_extensionalEq_iff_eq hE,
    forceInfiniteRealFormula_semantics hE, eq_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact and_congr_right fun _ => forall_congr' fun _ => and_imp
end Syntax

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

import FIMADModels.DowOmegaSplitting
import YesMetaZFC.Model.Forcing.Internal.Check.Omega

/-! The unbounded-name formula follows from the manuscript's original
injection-based infinitude. The forcing implication is proved for the same
formula and name environment, using native ZF validity and local implication
elimination, without replacing infinitude by a host predicate. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
theorem unboundedNameFormula_semantics {n} (hE : Extensional M) (ρ : Env M n)
    (w t : Project.Term n) : Project.Formula.satisfies ρ (unboundedNameFormula w t) ↔
      ∀ N, M.mem N (w.eval ρ) → ∃ k, M.mem k (w.eval ρ) ∧ AtLeast (M := M) N k ∧ M.mem k (t.eval ρ) := by
  simp only [unboundedNameFormula, nameTailFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    atLeastFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def infiniteToUnboundedBody : Project.Formula 1 2 :=
  .imp (Project.Formula.isOmega (.bound 1))
    (.imp (Internal.Syntax.SubsetFormula .newest (.bound 1))
      (.imp (Internal.Syntax.InfiniteFormula (.bound 1) .newest)
        (unboundedNameFormula (.bound 1) .newest)))

theorem infiniteToUnboundedBody_closed : infiniteToUnboundedBody.FreeClosed := by
  simp -implicitDefEqProofs [infiniteToUnboundedBody, Definitional.Formula.FreeClosed]

theorem infiniteToUnboundedBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 2) :
    Project.Formula.satisfies ρ infiniteToUnboundedBody := by
  simp only [infiniteToUnboundedBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Internal.Syntax.satisfies_SubsetFormula hZF.1,
    Internal.Syntax.satisfies_InfiniteFormula hZF.1, unboundedNameFormula_semantics hZF.1]
  intro hw hs hi N hN
  obtain ⟨k, hk, hNk, hkt⟩ := (Internal.infinite_iff_unbounded hZF
    ((Internal.omega_native_iff hZF.1 (ρ.bound 1)).mpr hw) hs).mp hi N hN
  exact ⟨k, hk, hNk.symm, hkt⟩

def infiniteToUnboundedSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose infiniteToUnboundedBody)
  (ObjectTheory.universalClose_closed _ infiniteToUnboundedBody_closed)
end Syntax

theorem forces_unbounded_of_infinite (hZF : M.Models SetTheory.ZF)
    {B R z p : M.Domain} (O : Cond_order_d M B R z) (ρ : Env M 2)
    (hρ : ∀ v : Project.Term 2, Name_d M B (v.eval ρ))
    (hp : M.mem p B) (hz : p ≠ z)
    (hOmega : Forces_d M B R z (Project.Formula.isOmega (.bound 1)) ρ p)
    (hSubset : Forces_d M B R z (Internal.Syntax.SubsetFormula .newest (.bound 1)) ρ p)
    (hInfinite : Forces_d M B R z (Internal.Syntax.InfiniteFormula (.bound 1) .newest) ρ p) :
    Forces_d M B R z (Syntax.unboundedNameFormula (.bound 1) .newest) ρ p := by
  have h := forces_zf_valid_l O hZF Syntax.infiniteToUnboundedBody
    Syntax.infiniteToUnboundedBody_closed
    (fun _ hN η => Syntax.infiniteToUnboundedBody_valid hN η) ρ (fun i => hρ (.bound i)) hp hz
  have h₁ := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1
    (forces_regular_l O hZF _ ρ hρ) hp hz h hOmega
  have h₂ := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1
    (forces_regular_l O hZF _ ρ hρ) hp hz h₁ hSubset
  exact forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1
    (forces_regular_l O hZF _ ρ hρ) hp hz h₂ hInfinite

theorem forces_subset_original_iff {B R z p : M.Domain} (ρ : Env M 2) :
    Forces_d M B R z (Internal.Syntax.SubsetFormula .newest (.bound 1)) ρ p ↔
      Forces_d M B R z (Project.Formula.subset .newest (.bound 1)) ρ p := Iff.rfl

theorem globally_forced_infinite_unbounded (hZF : M.Models SetTheory.ZF)
    {w B R c W t : M.Domain} (O : Cond_order_d M B R B)
    (hw : M.IsOmega w) (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (ht : Name_d M B t)
    (hSubset : ∀ p, M.mem p B → Forces_d M B R B
      (Project.Formula.subset .newest (.bound 1))
      ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p)
    (hInfinite : ∀ p, M.mem p B → Forces_d M B R B
      (Internal.Syntax.InfiniteFormula (.bound 1) .newest)
      ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p) : ForcesUnboundedName B R W t := by
  let ρ : Env M 2 := (⟨fun _ => W, fun _ => t⟩ : Env M 1).push t
  have hWN := check_name_l M (check_range_l M hZF) hc hW
  have hρ : ∀ v : Project.Term 2, Name_d M B (v.eval ρ) := by
    intro v
    cases v with
    | free _ => exact ht
    | bound i => exact Fin.cases ht (fun _ => hWN) i
  have hBind : (Project.Formula.isOmega .newest : Project.Formula 1 1).bind
      (fun _ : Fin 1 => (.bound 1 : Project.Term 2)) = Project.Formula.isOmega (.bound 1 : Project.Term 2) := by
    simp [Project.Formula.isOmega, Project.Formula.isInductive, Project.Formula.isEmpty,
      Project.Formula.isSuccessor, Project.Formula.forallMem, Project.Formula.extensionalEq,
      Project.Formula.subset, Definitional.Formula.bind, Definitional.Term.bind,
      Definitional.Term.liftSubstitution, Definitional.Term.newest, Definitional.Term.weaken,
      Definitional.Term.rename, Definitional.TermVector.bind, Project.Formula.pairArguments,
      Fin.cases, Fin.induction, Fin.induction.go]
  intro p hp
  have hpz : p ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  have hOmega := check_omega_force_l O hZF hw hc hW ⟨hp, hpz, hTop p hp⟩
  have hOmega' : Forces_d M B R B (Project.Formula.isOmega (.bound 1)) ρ p := by
    rw [← hBind, forces_bind_l hZF.1]
    exact (forces_env_l hZF.1 _ (Project.Formula.isOmega_freeClosed _ rfl)
      (⟨fun _ => W, fun _ => W⟩ : Env M 1)
      (Definitional.Env.substitute ρ (fun _ : Fin 1 => (.bound 1 : Project.Term 2)))
      (fun _ => rfl) p).mp hOmega
  exact forces_unbounded_of_infinite hZF O ρ hρ hp hpz hOmega'
    ((forces_subset_original_iff ρ).mpr (hSubset p hp)) (hInfinite p hp)

theorem countable_infinite_name_tests_exists (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W L : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hLc : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t ∧ ∀ p, M.mem p B →
      Forces_d M B R B (Project.Formula.subset .newest (.bound 1))
        ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p ∧
      Forces_d M B R B (Internal.Syntax.InfiniteFormula (.bound 1) .newest)
        ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p) :
    ∃ H, NameFamilyTests w A B R c L H := by
  apply countable_name_tests_exists hZFC hw O hB hR hc hTop hW hLc
  intro t htL
  obtain ⟨ht, hForce⟩ := hNames t htL
  exact ⟨ht, globally_forced_infinite_unbounded (ZFC.models_zf_l hZFC) O hw hc hTop hW ht
    (fun p hp => (hForce p hp).1) (fun p hp => (hForce p hp).2)⟩

theorem derives_infinite_name_unbounded : Project.Derives SetTheory.ZF Syntax.infiniteToUnboundedSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.infiniteToUnboundedBody (Syntax.infiniteToUnboundedBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

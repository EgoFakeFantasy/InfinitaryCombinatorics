import FIMADModels.DowConditionalTheorem

/-! Every internally countable family of infinite reals has an internal
omega-indexed covering function, including the empty and finite cases.
Unused indices are assigned omega. Only original ZF and the family's actual
injection into omega are used, so this also applies in generic quotients. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def InfiniteRealFamily (w F : M.Domain) : Prop :=
  ∀ t, M.mem t F → Internal.Subset M.mem t w ∧ Internal.Infinite M.mem w t

def CoversRealFamily (w F Q : M.Domain) : Prop :=
  Internal.FunctionOn M.mem Q w ∧
    (∀ n t, M.mem n w → Internal.Value M.mem Q n t →
      Internal.Subset M.mem t w ∧ Internal.Infinite M.mem w t) ∧
    ∀ t, M.mem t F → ∃ n, M.mem n w ∧ Internal.Value M.mem Q n t

namespace Syntax
def inverseOrOmegaSchema : BinarySchema 3 where
  body := .disj (.conj (.mem .newest (.bound 3))
    (Internal.Syntax.ValueFormula (.bound 2) .newest (.bound 1)))
    (.conj (Project.Formula.extensionalEq .newest (.bound 4))
      (.neg (.existsE (.conj (.mem .newest (.bound 4))
        (Internal.Syntax.ValueFormula (.bound 3) .newest (.bound 2))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]

theorem inverseOrOmegaSchema_semantics (hE : Extensional M) (ρ : Env M 3) (n t : M.Domain) :
    inverseOrOmegaSchema.denote ρ n t ↔
      (M.mem t (ρ.bound 1) ∧ Internal.Value M.mem (ρ.bound 0) t n) ∨
        (t = ρ.bound 2 ∧ ¬ ∃ x, M.mem x (ρ.bound 1) ∧ Internal.Value M.mem (ρ.bound 0) x n) := by
  simp only [BinarySchema.denote, inverseOrOmegaSchema, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_ValueFormula hE, Project.Formula.satisfies_extensionalEq_iff_eq hE,
    Project.Formula.satisfies_neg_iff, Project.Formula.satisfies_exists_iff]
  rfl

def infiniteRealFamilyFormula {n} (w F : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest F.weaken) (infiniteRealFormula w.weaken .newest))

def coversRealFamilyFormula {n} (w F Q : Project.Term n) : Project.Formula 1 n :=
  .conj (Internal.Syntax.FunctionOnFormula Q w)
    (.conj (.forallE (.forallE (.imp (.mem (.bound 1) w.weaken.weaken)
      (.imp (Internal.Syntax.ValueFormula Q.weaken.weaken (.bound 1) .newest)
        (infiniteRealFormula w.weaken.weaken .newest)))))
      (.forallE (.imp (.mem .newest F.weaken) (.existsE (.conj (.mem .newest w.weaken.weaken)
        (Internal.Syntax.ValueFormula Q.weaken.weaken .newest (.bound 1)))))))

derive_free_closed infiniteRealFamilyFormula
derive_free_closed coversRealFamilyFormula

theorem infiniteRealFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w F : Project.Term n) : Project.Formula.satisfies ρ (infiniteRealFamilyFormula w F) ↔
      InfiniteRealFamily (w.eval ρ) (F.eval ρ) := by
  simp only [infiniteRealFamilyFormula, InfiniteRealFamily,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, infiniteRealFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem coversRealFamilyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w F Q : Project.Term n) : Project.Formula.satisfies ρ (coversRealFamilyFormula w F Q) ↔
      CoversRealFamily (w.eval ρ) (F.eval ρ) (Q.eval ρ) := by
  simp only [coversRealFamilyFormula, CoversRealFamily, Project.Formula.satisfies_conj_iff,
    Internal.Syntax.satisfies_FunctionOnFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_ValueFormula hE, infiniteRealFormula_semantics hE,
    Project.Formula.satisfies_exists_iff, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem countable_real_family_enumeration (hZF : M.Models SetTheory.ZF)
    {w F : M.Domain} (hw : M.IsOmega w) (hF : InternalCountable w F)
    (hGood : InfiniteRealFamily w F) : ∃ Q, CoversRealFamily w F Q := by
  classical
  obtain ⟨j, hj⟩ := hF
  let I := Internal.pairInterpretation hZF
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push F).push j
  let φ := Syntax.inverseOrOmegaSchema
  have hφ n t := Syntax.inverseOrOmegaSchema_semantics hZF.1 ρ n t
  have total n (_ : M.mem n w) : ∃ t, φ.denote ρ n t := by
    by_cases he : ∃ t, M.mem t F ∧ Internal.Value M.mem j t n
    · obtain ⟨t, ht⟩ := he
      exact ⟨t, (hφ n t).mpr (Or.inl ht)⟩
    · exact ⟨w, (hφ n w).mpr (Or.inr ⟨rfl, he⟩)⟩
  have unique n (_ : M.mem n w) t t' (ht : φ.denote ρ n t) (ht' : φ.denote ρ n t') : t = t' := by
    rcases (hφ n t).mp ht with ht | ⟨ht, he⟩ <;>
      rcases (hφ n t').mp ht' with ht' | ⟨ht', he'⟩
    · exact hj.2.2 t t' n ht.2 ht'.2
    · exact False.elim (he' ⟨t, ht⟩)
    · exact False.elim (he ⟨t', ht'⟩)
    · exact ht.trans ht'.symm
  obtain ⟨V, hV⟩ := ZF.exists_functionalImageOn hZF φ ρ w total unique
  obtain ⟨Q, hQ, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun n t hn ht => (hV t).mpr ⟨n, hn, ht⟩)
  have values n t : Internal.Value M.mem Q n t ↔ M.mem n w ∧ φ.denote ρ n t :=
    (Internal.value_pairMember hZF Q n t).trans (he n t)
  have hFunction : Internal.FunctionOn M.mem Q w := by
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨n, t, hCode⟩ := hQ.1.1 p hp
      exact ⟨n, t, (hQ.2.1 n).mpr ⟨t, p, hCode, hp⟩, hCode⟩
    · intro n hn
      obtain ⟨t, _, hnt⟩ := hQ.2.2 n hn
      exact ⟨t, (Internal.value_pairMember hZF Q n t).mpr hnt,
        fun t' ht' => hQ.1.2 n t' t ((Internal.value_pairMember hZF Q n t').mp ht') hnt⟩
  have hiw : Internal.Infinite M.mem w w :=
    (Internal.infinite_iff_unbounded hZF ((Internal.omega_native_iff hZF.1 _).mpr hw)
      (fun _ h => h)).mpr (fun n hn => ⟨n, hn, Or.inr rfl, hn⟩)
  refine ⟨Q, hFunction, ?_, ?_⟩
  · intro n t _ hnt
    rcases (hφ n t).mp ((values n t).mp hnt).2 with ht | ⟨rfl, _⟩
    · exact hGood t ht.1
    · exact ⟨fun _ h => h, hiw⟩
  · intro t ht
    obtain ⟨n, htn, _⟩ := hj.1.2 t ht
    have hn := hj.2.1 t n htn
    exact ⟨n, hn, (values n t).mpr ⟨hn, (hφ n t).mpr (Or.inl ⟨ht, htn⟩)⟩⟩

namespace Syntax
def countableRealEnumerationBody : Project.Formula 1 2 :=
  .imp (Project.Formula.isOmega (.bound 1))
    (.imp (.existsE (Internal.Syntax.InjectionFormula .newest (.bound 1) (.bound 2)))
      (.imp (infiniteRealFamilyFormula (.bound 1) .newest)
        (.existsE (coversRealFamilyFormula (.bound 2) (.bound 1) .newest))))

theorem countableRealEnumerationBody_closed : countableRealEnumerationBody.FreeClosed := by
  simp -implicitDefEqProofs [countableRealEnumerationBody, Definitional.Formula.FreeClosed]

def countableRealEnumerationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose countableRealEnumerationBody)
  (ObjectTheory.universalClose_closed _ countableRealEnumerationBody_closed)

theorem countableRealEnumerationBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 2) :
    Project.Formula.satisfies ρ countableRealEnumerationBody := by
  simp only [countableRealEnumerationBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    Internal.Syntax.satisfies_InjectionFormula hZF.1,
    infiniteRealFamilyFormula_semantics hZF.1, coversRealFamilyFormula_semantics hZF.1]
  exact countable_real_family_enumeration hZF
end Syntax

theorem derives_countable_real_enumeration : Project.Derives SetTheory.ZF Syntax.countableRealEnumerationSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid _ (Syntax.countableRealEnumerationBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

import FIMADModels.DowFiniteTail
import YesMetaZFC.SetTheory.Card.CountableUnion

/-! Model-internal test families for common possible values. These predicates
quantify over actual internal sets and injection graphs, not over host
countable subsets of an externally standard omega. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def InternalCountable (w X : M.Domain) : Prop := ∃ J, Internal.Injection M.mem J X w

def MeetsTests (w B F : M.Domain) : Prop :=
  ∀ X, M.mem X F → Internal.Infinite M.mem w X → Internal.InfiniteInter M.mem w X B

def AvoidsValues (w A E p B : M.Domain) : Prop :=
  ∀ k, M.mem k B → AvoidValue w A E p k

def TestsWitness (w A E s F : M.Domain) : Prop :=
  InternalCountable w F ∧
  (∀ X, M.mem X F → Internal.Subset M.mem X w) ∧
  ∀ B, MeetsTests w B F → ∀ p, SameStem w A s p → AvoidsValues w A E p B →
    ∃ k, M.mem k w ∧ PossibleValue w A E s k

namespace Syntax
open Internal.Syntax
def meetsTestsFormula {n} (w B F : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest F.weaken)
    (.imp (InfiniteFormula w.weaken .newest) (InfiniteInterFormula w.weaken .newest B.weaken)))

def avoidsValuesFormula {n} (w A E p B : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest B.weaken)
    (avoidValueFormula w.weaken A.weaken E.weaken p.weaken .newest))

def testsWitnessFormula {n} (w A E s F : Project.Term n) : Project.Formula 1 n :=
  .conj (.existsE (InjectionFormula .newest F.weaken w.weaken))
    (.conj (.forallE (.imp (.mem .newest F.weaken) (SubsetFormula .newest w.weaken)))
      (.forallE (.imp (meetsTestsFormula w.weaken .newest F.weaken)
        (.forallE (.imp (sameStemFormula w.weaken.weaken A.weaken.weaken s.weaken.weaken .newest)
          (.imp (avoidsValuesFormula w.weaken.weaken A.weaken.weaken E.weaken.weaken .newest (.bound 1))
            (.existsE (.conj (.mem .newest w.weaken.weaken.weaken)
              (possibleValueFormula w.weaken.weaken.weaken A.weaken.weaken.weaken
                E.weaken.weaken.weaken s.weaken.weaken.weaken .newest)))))))))

derive_free_closed meetsTestsFormula
derive_free_closed avoidsValuesFormula
derive_free_closed testsWitnessFormula

theorem meetsTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w B F : Project.Term n) : Project.Formula.satisfies ρ (meetsTestsFormula w B F) ↔
      MeetsTests (w.eval ρ) (B.eval ρ) (F.eval ρ) := by
  simp only [meetsTestsFormula, MeetsTests, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    satisfies_InfiniteFormula hE, satisfies_InfiniteInterFormula hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem avoidsValuesFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E p B : Project.Term n) : Project.Formula.satisfies ρ (avoidsValuesFormula w A E p B) ↔
      AvoidsValues (w.eval ρ) (A.eval ρ) (E.eval ρ) (p.eval ρ) (B.eval ρ) := by
  simp only [avoidsValuesFormula, AvoidsValues, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    avoidValueFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem testsWitnessFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E s F : Project.Term n) : Project.Formula.satisfies ρ (testsWitnessFormula w A E s F) ↔
      TestsWitness (w.eval ρ) (A.eval ρ) (E.eval ρ) (s.eval ρ) (F.eval ρ) := by
  simp only [testsWitnessFormula, TestsWitness, InternalCountable,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_exists_iff,
    satisfies_InjectionFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    satisfies_SubsetFormula hE, meetsTestsFormula_semantics hE,
    sameStemFormula_semantics hE, avoidsValuesFormula_semantics hE,
    possibleValueFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem countable_test_image (hZFC : M.Models SetTheory.ZFC) {w X : M.Domain}
    {n} (φ : BinarySchema n) (ρ : Env M n)
    (hX : InternalCountable w X)
    (ht : ∀ x, M.mem x X → ∃ y, φ.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.denote ρ x y → φ.denote ρ x z → y = z) :
    ∃ Y, (∀ y, M.mem y Y ↔ ∃ x, M.mem x X ∧ φ.denote ρ x y) ∧
      InternalCountable w Y := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨Y, hY⟩ := ZF.exists_functionalImageOn hZF φ ρ X ht hu
  obtain ⟨F, hF, he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ ht hu
    (fun x y hx hxy => (hY y).mpr ⟨x, hx, hxy⟩)
  have hSurj : M.IsSetSurjectiveOnto I F X Y := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := (hY y).mp hy
    exact ⟨x, hx, (he x y).mpr ⟨hx, hxy⟩⟩
  obtain ⟨G, hG⟩ := ZFC.surjection_bound_l I hZFC hF hSurj
  obtain ⟨J, hJ⟩ := hX
  have hJ := (ForcingFinite.injection_correct hZF J X w).mp hJ
  obtain ⟨K, hK⟩ := ZF.exists_compositionInjection hZF I hG hJ
  exact ⟨Y, hY, K, (ForcingFinite.injection_correct hZF K Y w).mpr hK⟩

theorem empty_tests (hZF : M.Models SetTheory.ZF) {w A E s k : M.Domain}
    (hk : M.mem k w) (hPossible : PossibleValue w A E s k) : ∃ F, TestsWitness w A E s F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨F, hF⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨J, hJ⟩ := ZF.exists_inclusionInjection hZF I (source := F) (target := w)
    (fun x hx => False.elim (hF x hx))
  exact ⟨F, ⟨J, (ForcingFinite.injection_correct hZF J F w).mpr hJ⟩,
    (fun X hx => False.elim (hF X hx)), fun _ _ _ _ _ => ⟨k, hk, hPossible⟩⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

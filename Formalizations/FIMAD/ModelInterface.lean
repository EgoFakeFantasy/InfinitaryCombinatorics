import Formalizations.FIMAD.CheckedZFC
import Formalizations.FIMAD.FirstOrderSemantics
import Formalizations.FIMAD.Metatheory
import YesMetaZFC.Logic.FirstOrder.Derivation.Soundness

/-! Concrete contracts for the remaining model constructions. Model witnesses
are explicit hypotheses, not declarations asserting that such models exist.
The target theory and sentence are fixed to ZFC and infinite FI MAD existence. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD
namespace ModelInterface
open YesMetaZFC YesMetaZFC.SetTheory
open Logic.FirstOrder
open Definitional.Project (fo_sentence fo_theory)
universe u v

def zfcTheory : Theory signature := fo_theory CheckedZFC.Axiom

def existenceSentence : Formula signature := fo_sentence Internal.Syntax.sentence

theorem existenceSentence_admissible : Formula.Admissible existenceSentence :=
  Internal.Syntax.sentence_is_firstOrder.1

def ModelsZFC (M : SetTheory.Structure.{u}) : Prop :=
  ∀ env : Env (Internal.FirstOrderBridge.toFirstOrder M), zfcTheory.Models env

noncomputable def defaultEnv (M : SetTheory.Structure.{u}) :
    Env (Internal.FirstOrderBridge.toFirstOrder M) where
  boundVal := fun _ _ => Classical.choice M.nonempty
  freeVal := fun _ _ => Classical.choice M.nonempty
  boundSort := fun _ _ => trivial
  freeSort := fun _ _ => trivial

theorem positive_consistent_of_model {M : SetTheory.Structure.{u}}
    (hM : ModelsZFC M) (hExt : Extensional M) (hE : Internal.ExistsFIMAD M.mem) :
    Derives.Consistent zfcTheory [existenceSentence] := by
  intro hFalse
  have hsat : Formula.satisfies (defaultEnv M) existenceSentence :=
    (Internal.FirstOrderBridge.satisfies_fimad_sentence hExt _).mpr hE
  have hctx : Context.Satisfied (defaultEnv M) [existenceSentence] := by
    intro φ hφ
    have heq : φ = existenceSentence := List.mem_singleton.mp hφ
    exact heq ▸ hsat
  exact hFalse.sound (defaultEnv M) (hM _) hctx

theorem negative_consistent_of_model {M : SetTheory.Structure.{u}}
    (hM : ModelsZFC M) (hExt : Extensional M) (hE : ¬ Internal.ExistsFIMAD M.mem) :
    Derives.Consistent zfcTheory [Formula.neg existenceSentence] := by
  intro hFalse
  have hsat : Formula.satisfies (defaultEnv M) (Formula.neg existenceSentence) := by
    simp only [Formula.satisfies]
    exact fun h => hE ((Internal.FirstOrderBridge.satisfies_fimad_sentence hExt _).mp h)
  have hctx : Context.Satisfied (defaultEnv M) [Formula.neg existenceSentence] := by
    intro φ hφ
    have heq : φ = Formula.neg existenceSentence := List.mem_singleton.mp hφ
    exact heq ▸ hsat
  exact hFalse.sound (defaultEnv M) (hM _) hctx

/-- Once actual models are supplied, the public proof kernel rules out both
ZFC derivations. This theorem does not construct either model. -/
theorem independent_of_models {M : SetTheory.Structure.{u}} {N : SetTheory.Structure.{v}}
    (hM : ModelsZFC M) (hMext : Extensional M) (hME : Internal.ExistsFIMAD M.mem)
    (hN : ModelsZFC N) (hNext : Extensional N) (hNE : ¬ Internal.ExistsFIMAD N.mem) :
    Metatheory.Independent zfcTheory existenceSentence :=
  Metatheory.independent_of_consistent_extensions existenceSentence_admissible
    (positive_consistent_of_model hM hMext hME)
    (negative_consistent_of_model hN hNext hNE)

end ModelInterface
end InfinitaryCombinatorics.Formalizations.FIMAD

import Formalizations.FIMAD.SetTheorySentence
import FIMADModels.BooleanQuotient
import FIMADModels.InfiniteSplitting
import FIMADModels.ObjectTheory
import FIMADModels.ForcingFinite
import FIMADModels.IterationSchema
import YesMetaZFC.Model.SetTheory.ProjectSemantics

/-! The actual FI MAD sentence in the public typed kernel and Boolean name model.
The ZFC certificate is supplied by the upstream construction. Truth or falsity
of FI MAD existence in a particular Boolean algebra remains a separate theorem.
-/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.Logic.FirstOrder
open YesMetaZFC.Model YesMetaZFC.Model.Boolean
open Definitional.Project

abbrev existenceSentence : YesMetaZFC.Logic.FirstOrder.Sentence ℒ :=
  fo_sentence Internal.Syntax.sentence

/-- The typed sentence has exactly the membership semantics of the manuscript. -/
theorem native_semantics {M : YesMetaZFC.Logic.FirstOrder.Structure ℒ}
    (hExt : Extensional (FirstOrderSemantics.reduct M)) :
    existenceSentence.TrueIn M ↔
      Internal.ExistsFIMAD (FirstOrderSemantics.reduct M).mem :=
  (FirstOrderSemantics.sentence_correct hExt Internal.Syntax.sentence).trans
    (Internal.Syntax.sentence_semantics hExt)

universe u
variable {B : Type u} (𝔹 : CB_alg B)

noncomputable def existenceValue : B :=
  BV_str.value 𝔹 (name_structure 𝔹) existenceSentence Env.empty

/-- Both evaluators compute the same Boolean value of the concrete sentence. -/
theorem value_correct :
    existenceValue 𝔹 = BV_project.value 𝔹 Internal.Syntax.sentence.formula
      (FirstOrderSemantics.projectEnv Env.empty (fun _ => BV_graph.empty 𝔹.toPO_bot)) :=
  BV_project.formula_correct 𝔹 _ Internal.Syntax.sentence.freeClosed Env.empty
    (fun _ => BV_graph.empty 𝔹.toPO_bot)

theorem holds_iff_top :
    (name_model 𝔹).holds existenceSentence ↔ 𝔹.le 𝔹.top (existenceValue 𝔹) := by
  constructor
  · exact fun h => h Env.empty
  · intro h ρ
    rw [Env.empty_unique ρ]
    exact h

/-- The complete Boolean name construction actually verifies ZFC. -/
theorem name_model_satisfies_zfc : (name_model 𝔹).models zfcTheory :=
  CheckedBooleanZFC.models_zfc 𝔹

def withSentence (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ) : Theory ℒ :=
  fun ψ => zfcTheory ψ ∨ ψ = φ

/-- A top-valued sentence gives consistency of the actual extended ZFC theory. -/
theorem consistent_extension (hNontrivial : ¬ 𝔹.le 𝔹.top 𝔹.bot)
    (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ) (hφ : (name_model 𝔹).holds φ) :
    Derives.Consistent (withSentence φ) ([] : Context ℒ []) := by
  apply (name_rules 𝔹).consistent_of_models
  · intro h
    exact hNontrivial (h Env.empty)
  · intro ψ hψ
    rcases hψ with hψ | rfl
    · exact CheckedBooleanZFC.models_zfc 𝔹 ψ hψ
    · exact hφ

theorem positive_consistency (hNontrivial : ¬ 𝔹.le 𝔹.top 𝔹.bot)
    (hE : 𝔹.le 𝔹.top (existenceValue 𝔹)) :
    Derives.Consistent (withSentence existenceSentence) ([] : Context ℒ []) :=
  consistent_extension 𝔹 hNontrivial _ ((holds_iff_top 𝔹).mpr hE)

theorem negative_consistency (hNontrivial : ¬ 𝔹.le 𝔹.top 𝔹.bot)
    (hE : 𝔹.le 𝔹.top (𝔹.neg (existenceValue 𝔹))) :
    Derives.Consistent (withSentence (.neg existenceSentence)) ([] : Context ℒ []) := by
  apply consistent_extension 𝔹 hNontrivial
  intro ρ
  rw [Env.empty_unique ρ]
  exact hE

/-- Nonzero truth of E suffices for an actual extensional ZFC model of internal E. -/
theorem positive_model_of_nonzero (hE : existenceValue 𝔹 ≠ 𝔹.bot) :
    ∃ M : YesMetaZFC.Logic.FirstOrder.Structure.{0,0,0,u+1} ℒ,
      Theory.Models M zfcTheory ∧ Extensional (FirstOrderSemantics.reduct M) ∧
      Internal.ExistsFIMAD (FirstOrderSemantics.reduct M).mem := by
  obtain ⟨M, hM, hExt, hφ⟩ := BooleanQuotient.model_of_nonzero 𝔹 existenceSentence hE
  exact ⟨M, hM, hExt, (native_semantics hExt).mp hφ⟩

/-- A Boolean value of E below top produces a genuine model of its negation. -/
theorem negative_model_of_not_top (hE : existenceValue 𝔹 ≠ 𝔹.top) :
    ∃ M : YesMetaZFC.Logic.FirstOrder.Structure.{0,0,0,u+1} ℒ,
      Theory.Models M zfcTheory ∧ Extensional (FirstOrderSemantics.reduct M) ∧
      ¬ Internal.ExistsFIMAD (FirstOrderSemantics.reduct M).mem := by
  have hn : 𝔹.neg (existenceValue 𝔹) ≠ 𝔹.bot := by
    intro h
    apply hE
    rw [← 𝔹.neg_neg (existenceValue 𝔹), h]
  obtain ⟨M, hM, hExt, hφ⟩ := BooleanQuotient.model_of_nonzero 𝔹 (.neg existenceSentence) hn
  exact ⟨M, hM, hExt, fun h => hφ ((native_semantics hExt).mpr h)⟩

/-- Consistency needs only a nonzero value, not validity at top. -/
theorem consistency_of_nonzero (φ : YesMetaZFC.Logic.FirstOrder.Sentence ℒ)
    (hφ : BV_str.value 𝔹 (name_structure 𝔹) φ Env.empty ≠ 𝔹.bot) :
    Derives.Consistent (withSentence φ) ([] : Context ℒ []) := by
  obtain ⟨M, hM, _, hφ⟩ := BooleanQuotient.model_of_nonzero 𝔹 φ hφ
  apply Native.consistent M
  intro ψ hψ
  rcases hψ with hψ | rfl
  · exact hM ψ hψ
  · exact hφ


end InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels

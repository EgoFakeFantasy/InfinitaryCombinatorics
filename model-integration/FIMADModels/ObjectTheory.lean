import FIMADModels.FiniteUnbounded
import Formalizations.FIMAD.CheckedZFC
import YesMetaZFC.Model.SetTheory.ProjectSemantics
import YesMetaZFC.Model.Henkin.StrongCompleteness
import YesMetaZFC.Model.Henkin.SyntaxNatCoding

/-! Object-theory endpoints in the original typed first-order derivation kernel.
The language is pure membership with logical equality, the background is ZF,
and the target sentences use the manuscript's original finite-injection coding.
Model semantics are transferred through a checked language/reduct bridge and
strong completeness for the countable membership signature. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.ObjectTheory
open YesMetaZFC YesMetaZFC.SetTheory
open Definitional Definitional.Project
open YesMetaZFC.Logic.FirstOrder
namespace P
open Internal.Syntax

def boundedFormula {depth : Nat} (w a : Project.Term depth) : Project.Formula 1 depth :=
  .existsE (.conj (.mem (.bound 0) w.weaken) (SubsetFormula a.weaken (.bound 0)))

theorem boundedFormula_closed {depth : Nat} (w a : Project.Term depth)
    (hw : w.freeSupport = []) (ha : a.freeSupport = []) :
    (boundedFormula w a).FreeClosed := by
  simp only [boundedFormula, SubsetFormula, Definitional.Formula.FreeClosed,
    Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, hw, ha, and_self]
  all_goals trivial

def infiniteUnboundedBody : Project.Formula 1 2 :=
  .imp (.conj (OmegaFormula (.bound 1)) (SubsetFormula (.bound 0) (.bound 1)))
    (.iff (InfiniteFormula (.bound 1) (.bound 0)) (UnboundedFormula (.bound 1) (.bound 0)))

def finiteBoundedBody : Project.Formula 1 2 :=
  .imp (.conj (OmegaFormula (.bound 1)) (SubsetFormula (.bound 0) (.bound 1)))
    (.iff (FiniteFormula (.bound 1) (.bound 0)) (boundedFormula (.bound 1) (.bound 0)))

theorem infiniteUnboundedBody_closed : infiniteUnboundedBody.FreeClosed := by
  simp only [infiniteUnboundedBody, Definitional.Formula.FreeClosed]
  exact ⟨⟨closed_OmegaFormula _ rfl, closed_SubsetFormula _ _ rfl rfl⟩,
    closed_InfiniteFormula _ _ rfl rfl, closed_UnboundedFormula _ _ rfl rfl⟩

theorem finiteBoundedBody_closed : finiteBoundedBody.FreeClosed := by
  simp only [finiteBoundedBody, Definitional.Formula.FreeClosed]
  exact ⟨⟨closed_OmegaFormula _ rfl, closed_SubsetFormula _ _ rfl rfl⟩,
    closed_FiniteFormula _ _ rfl rfl, boundedFormula_closed _ _ rfl rfl⟩

def infiniteUnbounded : Project.Sentence :=
  Project.Sentence.ofFormula (.forallE (.forallE infiniteUnboundedBody)) (by simpa only [Definitional.Formula.FreeClosed] using infiniteUnboundedBody_closed)

def finiteBounded : Project.Sentence :=
  Project.Sentence.ofFormula (.forallE (.forallE finiteBoundedBody)) (by simpa only [Definitional.Formula.FreeClosed] using finiteBoundedBody_closed)

universe u
variable {M : SetTheory.Structure.{u}}

theorem boundedFormula_semantics (hExt : Extensional M) {depth : Nat}
    (env : SetTheory.Env M depth) (w a : Project.Term depth) :
    Project.Formula.satisfies env (boundedFormula w a) ↔
      Internal.Bounded (M := M) (w.eval env) (a.eval env) := by
  simp only [boundedFormula, Internal.Bounded, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    satisfies_SubsetFormula hExt, Definitional.Term.eval_weaken]
  rfl

theorem infiniteUnbounded_semantics (hExt : Extensional M) :
    M.SatisfiesSentence infiniteUnbounded ↔
      ∀ w a, Internal.Omega M.mem w → Internal.Subset M.mem a w →
        (Internal.Infinite M.mem w a ↔ Internal.Unbounded M.mem w a) := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  simp only [infiniteUnbounded,
    Project.Sentence.ofFormula, infiniteUnboundedBody, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_iff_iff, satisfies_OmegaFormula hExt,
    satisfies_SubsetFormula hExt, satisfies_InfiniteFormula hExt,
    satisfies_UnboundedFormula hExt]
  constructor
  · intro h w a
    obtain ⟨z⟩ := M.nonempty
    exact fun hw ha => h (fun _ => z) w a ⟨hw, ha⟩
  · intro h free w a
    exact fun ⟨hw, ha⟩ => h w a hw ha

theorem finiteBounded_semantics (hExt : Extensional M) :
    M.SatisfiesSentence finiteBounded ↔
      ∀ w a, Internal.Omega M.mem w → Internal.Subset M.mem a w →
        (Internal.Finite M.mem w a ↔ Internal.Bounded (M := M) w a) := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  simp only [finiteBounded,
    Project.Sentence.ofFormula, finiteBoundedBody, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_iff_iff, satisfies_OmegaFormula hExt,
    satisfies_SubsetFormula hExt, satisfies_FiniteFormula hExt, boundedFormula_semantics hExt]
  constructor
  · intro h w a
    obtain ⟨z⟩ := M.nonempty
    exact fun hw ha => h (fun _ => z) w a ⟨hw, ha⟩
  · intro h free w a
    exact fun ⟨hw, ha⟩ => h w a hw ha
end P

/-- An explicit countable symbol coding for the pure membership signature. -/
def membershipSymbols : Automation.SyntaxNatCoding.SymbolCoding ℒ where
  sort := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩
  function := { encode := fun f => nomatch f
                injective := by intro f; cases f }
  relation := ⟨fun _ => 0, by intro a b _; cases a; cases b; rfl⟩

noncomputable def membershipSchedule : Completeness.Henkin.Schedule ℒ :=
  Automation.SyntaxNatCoding.schedule membershipSymbols

universe u
/-- Derive extensionality of the actual reduct from the typed ZF axiom. -/
theorem native_extensional_of_zf {M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : Theory.Models M (fo_theory SetTheory.ZF)) : Extensional (FirstOrderSemantics.reduct M) := by
  have h := hM _ ⟨Axioms.extensionality, ZF.Axiom.extensionality, rfl⟩
  simp only [Logic.FirstOrder.Formula.TrueIn, fo_sentence, Axioms.extensionality,
    Project.Sentence.ofFormula, fo_formula, fo_mem, fo_term, fo_bound_variable,
    Logic.FirstOrder.Formula.satisfies, Arguments.eval, Logic.FirstOrder.Term.eval,
    Project.Term.newest, Project.Term.weaken, Definitional.Term.newest,
    Definitional.Term.weaken, Definitional.Term.rename, Definitional.Term.bind,
    Project.Formula.extensionalEq, Project.Formula.pairArguments] at h
  exact ⟨h⟩

theorem native_zf_of_typed {M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : Theory.Models M (fo_theory SetTheory.ZF)) :
    (FirstOrderSemantics.reduct M).Models SetTheory.ZF :=
  (FirstOrderSemantics.models_iff (native_extensional_of_zf hM) SetTheory.ZF).mp hM

/-- The ZFC bridge uses the same typed/native reduct and no extra model premise. -/
theorem native_zfc_of_typed {M : Logic.FirstOrder.Structure.{0,0,0,u} ℒ}
    (hM : Theory.Models M (fo_theory SetTheory.ZFC)) :
    (FirstOrderSemantics.reduct M).Models SetTheory.ZFC := by
  have hZF : Theory.Models M (fo_theory SetTheory.ZF) := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact hM _ ⟨t, ZFC.Axiom.zf ht, rfl⟩
  exact (FirstOrderSemantics.models_iff (native_extensional_of_zf hZF) SetTheory.ZFC).mp hM

/-- Original ZF transfer at the exact model universe required by completeness. -/
theorem derives_of_native_zf_models (s : Project.Sentence)
    (h : ∀ N : SetTheory.Structure.{0}, N.Models SetTheory.ZF → N.SatisfiesSentence s) :
    Project.Derives SetTheory.ZF s := by
  apply Completeness.strong_completeness membershipSchedule
  intro M hM
  have hN := native_zf_of_typed hM
  exact (FirstOrderSemantics.sentence_correct hN.1 s).mpr (h _ hN)

/-- Original ZFC transfer for the same countable pure-membership signature. -/
theorem derives_of_native_zfc_models (s : Project.Sentence)
    (h : ∀ N : SetTheory.Structure.{0}, N.Models SetTheory.ZFC → N.SatisfiesSentence s) :
    Project.Derives SetTheory.ZFC s := by
  apply Completeness.strong_completeness membershipSchedule
  intro M hM
  have hN := native_zfc_of_typed hM
  exact (FirstOrderSemantics.sentence_correct hN.1 s).mpr (h _ hN)
/-- The conclusion is an actual proof in the original Derives kernel. -/
theorem derives_infinite_iff_unbounded : Project.Derives SetTheory.ZF P.infiniteUnbounded := by
  apply Completeness.strong_completeness membershipSchedule
  intro M hM
  have hZF := native_zf_of_typed hM
  apply (FirstOrderSemantics.sentence_correct hZF.1 P.infiniteUnbounded).mpr
  exact (P.infiniteUnbounded_semantics hZF.1).mpr
    (fun _ _ hw ha => Internal.infinite_iff_unbounded hZF hw ha)

/-- The boundedness/finite-injection equivalence also has an object proof. -/
theorem derives_finite_iff_bounded : Project.Derives SetTheory.ZF P.finiteBounded := by
  apply Completeness.strong_completeness membershipSchedule
  intro M hM
  have hZF := native_zf_of_typed hM
  apply (FirstOrderSemantics.sentence_correct hZF.1 P.finiteBounded).mpr
  exact (P.finiteBounded_semantics hZF.1).mpr
    (fun _ _ hw ha => Internal.finite_iff_bounded hZF hw ha)

/-- Close all remaining bound parameters; external schema indices stay external. -/
def universalClose : {n : Nat} → Project.Formula 1 n → Project.Formula 1 0
  | 0, φ => φ
  | _+1, φ => universalClose (.forallE φ)


theorem universalClose_closed {n} (φ : Project.Formula 1 n) (h : φ.FreeClosed) :
    (universalClose φ).FreeClosed := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih (.forallE φ) (by simpa only [Definitional.Formula.FreeClosed] using h)

theorem universalClose_valid {N : SetTheory.Structure.{u}} {n} (φ : Project.Formula 1 n)
    (h : ∀ ρ : Env N n, Project.Formula.satisfies ρ φ) :
    ∀ free, Project.Formula.satisfies (⟨Fin.elim0, free⟩ : Env N 0) (universalClose φ) := by
  induction n with
  | zero => exact fun free => h ⟨Fin.elim0, free⟩
  | succ n ih =>
    apply ih (.forallE φ)
    intro ρ
    rw [Project.Formula.satisfies_forall_iff]
    exact fun a => h (ρ.push a)
end InfinitaryCombinatorics.Formalizations.FIMAD.ObjectTheory

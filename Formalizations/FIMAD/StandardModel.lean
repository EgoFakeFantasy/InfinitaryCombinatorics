import Formalizations.FIMAD.StandardTransfer
import Formalizations.FIMAD.ModelInterface
import YesMetaZFC.SetTheory.Separation
import YesMetaZFC.SetTheory.Collection

/-! The standard well-founded set universe as a model of the precise checked
ZFC theory used by the project's proof kernel, including both full schemas. -/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Standard
open YesMetaZFC YesMetaZFC.SetTheory
open Definitional.Project
universe u

def model : SetTheory.Structure.{u+1} where
  Domain := ZFSet.{u}
  nonempty := ⟨∅⟩
  mem := mem

theorem model_extensional : Extensional model.{u} where
  eq_of_same_members _ _ h := ZFSet.ext h

theorem collection (P : ZFSet.{u} → ZFSet.{u} → Prop) (a : ZFSet.{u})
    (h : ∀ x ∈ a, ∃ y, P x y) : ∃ b : ZFSet, ∀ x ∈ a, ∃ y ∈ b, P x y := by
  classical
  letI : Small.{u} ↥(a : Set ZFSet) := ZFSet.small_coe a
  let f : ↥(a : Set ZFSet) → ZFSet := fun x => (h x x.property).choose
  refine ⟨ZFSet.range f, fun x hx => ?_⟩
  exact ⟨f ⟨x, hx⟩, ZFSet.mem_range_self (f := f) ⟨x, hx⟩, (h x hx).choose_spec⟩

theorem choice_set (A : ZFSet.{u})
    (hne : ∀ a ∈ A, ∃ x, x ∈ a)
    (hd : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ x, x ∈ a ∧ x ∈ b) :
    ∃ c : ZFSet, ∀ a ∈ A, ∃ x, (x ∈ c ∧ x ∈ a) ∧ ∀ y, (y ∈ c ∧ y ∈ a) → y = x := by
  classical
  letI : Small.{u} ↥(A : Set ZFSet) := ZFSet.small_coe A
  let f : ↥(A : Set ZFSet) → ZFSet := fun a => (hne a a.property).choose
  have hf (a : ↥(A : Set ZFSet)) : f a ∈ a.val := (hne a a.property).choose_spec
  refine ⟨ZFSet.range f, fun a ha => ⟨f ⟨a, ha⟩,
    ⟨ZFSet.mem_range_self (f := f) ⟨a, ha⟩, hf ⟨a, ha⟩⟩, ?_⟩⟩
  rintro y ⟨hy, hya⟩
  obtain ⟨b, rfl⟩ := ZFSet.mem_range.mp hy
  have hba : b.val = a := by
    by_contra h
    exact hd b b.property a ha h ⟨f b, hf b, hya⟩
  exact congrArg f (Subtype.ext hba)

attribute [local simp] Formula.satisfies_forall_iff Formula.satisfies_exists_iff
  Formula.satisfies_mem_iff Formula.satisfies_neg_iff Formula.satisfies_conj_iff
  Formula.satisfies_disj_iff Formula.satisfies_imp_iff Formula.satisfies_iff_iff
  Formula.satisfies_subset_iff Formula.satisfies_extensionalEq_iff

@[local simp] private theorem ext_eq (x y : ZFSet.{u}) :
    (∀ z, z ∈ x ↔ z ∈ y) ↔ x = y := ZFSet.ext_iff.symm

theorem project_zfc (s : Sentence) (hs : CheckedZFC.Axiom s) (env : Env model.{u} 0) :
    Formula.satisfies env s.formula := by
  cases hs with
  | separation schema =>
    change Formula.satisfies env (Formula.forallClosure _ (Axioms.Schema.separationCore schema))
    have henv : env = ⟨Fin.elim0, env.free⟩ := by cases env; congr; exact funext (fun i => Fin.elim0 i)
    rw [henv, Formula.satisfies_forallClosure_iff]
    intro bound
    apply (Axioms.Schema.separation_sat_iff_d _ schema).mpr
    intro a
    exact ⟨ZFSet.sep (fun x => Formula.satisfies ((⟨bound, env.free⟩ : Env model _).push x)
      schema.body) a, fun x => ZFSet.mem_sep⟩
  | collection schema =>
    change Formula.satisfies env (Formula.forallClosure _ (Axioms.Schema.collectionCore schema))
    have henv : env = ⟨Fin.elim0, env.free⟩ := by cases env; congr; exact funext (fun i => Fin.elim0 i)
    rw [henv, Formula.satisfies_forallClosure_iff]
    intro bound
    apply (Axioms.Schema.collection_sat_iff_d _ schema).mpr
    exact collection _
  | extensionality =>
    simp [CheckedZFC.extensionality, Sentence.ofFormula, Term.newest, model, mem]
  | emptySet =>
    simp only [CheckedZFC.emptySet, Sentence.ofFormula, Formula.satisfies_exists_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
    change ∃ a : ZFSet.{u}, ∀ x, x ∉ a
    exact ⟨∅, ZFSet.notMem_empty⟩
  | pairing =>
    simp [CheckedZFC.pairing, Sentence.ofFormula, Term.newest, model, mem]
    intro x y
    exact ⟨{x, y}, fun z => ZFSet.mem_pair⟩
  | union =>
    simp [CheckedZFC.union, Sentence.ofFormula, Term.newest, model, mem]
    exact fun a => ⟨ZFSet.sUnion a, fun _ => ZFSet.mem_sUnion⟩
  | powerSet =>
    simp [CheckedZFC.powerSet, Sentence.ofFormula, Term.newest, model, mem]
    exact fun a => ⟨ZFSet.powerset a, fun _ => ZFSet.mem_powerset⟩
  | infinity =>
    simpa [CheckedZFC.infinity, Sentence.ofFormula, Term.newest, model, mem,
      Internal.Inductive, Internal.Empty, Internal.Succ] using
      (⟨ZFSet.omega, omega.1⟩ : ∃ w : ZFSet.{u}, Internal.Inductive mem w)
  | foundation =>
    simp only [CheckedZFC.foundation, Sentence.ofFormula, Formula.satisfies_forall_iff,
      Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff, Formula.satisfies_mem_iff]
    change ∀ a : ZFSet.{u}, (∃ x, x ∈ a) → ∃ b, b ∈ a ∧ ∀ x, x ∈ a → x ∉ b
    intro a ha
    have hne : a ≠ ∅ := by rintro rfl; simp at ha
    obtain ⟨b, hb, heq⟩ := ZFSet.regularity a hne
    exact ⟨b, hb, fun x hxa hxb => ZFSet.notMem_empty x
      (heq ▸ ZFSet.mem_inter.mpr ⟨hxa, hxb⟩)⟩
  | choice =>
    simp [CheckedZFC.choice, Sentence.ofFormula, Term.newest, Formula.extensionalNe, model, mem]
    intro A hne hd
    have hd' : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ x, x ∈ a ∧ x ∈ b := by
      rintro a ha b hb hne ⟨x, hxa, hxb⟩
      exact hd a ha b hb hne x hxa hxb
    simpa only [and_imp] using choice_set A hne hd'

theorem models_zfc : ModelInterface.ModelsZFC model.{u} := by
  intro env φ hφ
  obtain ⟨s, hs, rfl⟩ := hφ
  exact (Internal.FirstOrderBridge.satisfies_formula model_extensional s.formula env).mpr
    (project_zfc s hs _)

/-- The actual closed first-order sentence has exactly its intended host meaning. -/
theorem satisfies_sentence_iff
    (env : Logic.FirstOrder.Env (Internal.FirstOrderBridge.toFirstOrder model.{u})) :
    Logic.FirstOrder.Formula.satisfies env ModelInterface.existenceSentence ↔ ExistsFIMAD :=
  (Internal.FirstOrderBridge.satisfies_fimad_sentence model_extensional env).trans existsFIMAD_iff

theorem positive_consistency_of_CH
    (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) :
    Logic.FirstOrder.Derives.Consistent ModelInterface.zfcTheory [ModelInterface.existenceSentence] :=
  ModelInterface.positive_consistent_of_model models_zfc.{0} model_extensional
    (existsFIMAD_of_CH hCH)

theorem negative_consistency_of_s_lt_ap
    (h : R0.splittingNumber < almostDisjointSeparationNumber) :
    Logic.FirstOrder.Derives.Consistent ModelInterface.zfcTheory
      [Logic.FirstOrder.Formula.neg ModelInterface.existenceSentence] :=
  ModelInterface.negative_consistent_of_model models_zfc.{0} model_extensional
    (not_existsFIMAD_of_s_lt_ap h)

theorem positive_consistency_of_ap_eq_s_eq_continuum
    (hap : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0)
    (hs : R0.splittingNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0) :
    Logic.FirstOrder.Derives.Consistent ModelInterface.zfcTheory [ModelInterface.existenceSentence] :=
  ModelInterface.positive_consistent_of_model models_zfc.{0} model_extensional
    (existsFIMAD_of_ap_eq_s_eq_continuum hap hs)

end InfinitaryCombinatorics.Formalizations.FIMAD.Standard

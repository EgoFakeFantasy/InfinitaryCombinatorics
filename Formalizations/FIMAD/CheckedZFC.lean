import YesMetaZFC.SetTheory.Axioms.Common

/-! The same fixed ZFC formulas as the pinned upstream presentation, with
closure certificates checked by kernel reduction. The separation and
collection schemas are reused unchanged from the upstream library. -/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace InfinitaryCombinatorics.Formalizations.FIMAD.CheckedZFC
open YesMetaZFC YesMetaZFC.SetTheory

/-- 外延性公理。 -/
def extensionality : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ left right, (∀ element, element ∈ left ↔ element ∈ right) → left = right⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Term.newest])
/-- 空集公理。 -/
def emptySet : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∃ empty, ∀ element, element ∉ empty⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Term.newest])
/-- 配对公理。 -/
def pairing : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ left right, ∃ pair, ∀ element,
    element ∈ pair ↔ (element = left ∨ element = right)⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Term.newest])
/-- 并集公理。 -/
def union : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ family, ∃ union, ∀ element,
    element ∈ union ↔ ∃ member ∈ family, element ∈ member⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Formula.existsMem, Definitional.Project.Term.newest])
/-- 幂集公理。 -/
def powerSet : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ set, ∃ power, ∀ subset,
    subset ∈ power ↔ subset ⊆ set⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Term.newest])
/-- 无穷公理。 -/
def infinity : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∃ omegaSet, (∃ empty, (∀ element, element ∉ empty) ∧ empty ∈ omegaSet) ∧ (∀ set ∈ omegaSet, ∃ successor, ((∀ element,
        element ∈ successor ↔ (element ∈ set ∨ element = set)) ∧
        successor ∈ omegaSet))⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Formula.forallMem, Definitional.Project.Term.newest])
/-- 正则/基础公理。 -/
def foundation : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ set, (∃ element, element ∈ set) →
      ∃ minimal ∈ set, ∀ element ∈ set, element ∉ minimal⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Formula.forallMem, Definitional.Project.Formula.existsMem, Definitional.Project.Term.newest])
/-- 选择公理的选择集形式。 -/
def choice : Definitional.Project.Sentence :=
  Definitional.Project.Sentence.ofFormula (set! ⟪∀ family, ((∀ member ∈ family, ∃ element, element ∈ member) ∧ (∀ first ∈ family, ∀ second ∈ family,
        first ≠ second →
          ¬ (∃ element, element ∈ first ∧ element ∈ second))) → ∃ choice,
      ∀ member ∈ family, ∃ selected, ((selected ∈ choice ∧ selected ∈ member) ∧ (∀ other, (other ∈ choice ∧ other ∈ member) → other = selected))⟫) (by simp [Definitional.Formula.FreeClosed, Definitional.Project.Formula.extensionalNe, Definitional.Project.Formula.forallMem, Definitional.Project.Term.newest])

/-- ZFC in the upstream full separation/full collection presentation. -/
inductive Axiom : Definitional.Project.Theory where
  | extensionality : Axiom extensionality
  | emptySet : Axiom emptySet
  | pairing : Axiom pairing
  | union : Axiom union
  | powerSet : Axiom powerSet
  | infinity : Axiom infinity
  | foundation : Axiom foundation
  | choice : Axiom choice
  | separation {n : Nat} (schema : Definitional.Project.UnarySchema n) : Axiom (Axioms.Schema.separation schema)
  | collection {n : Nat} (schema : Definitional.Project.BinarySchema n) : Axiom (Axioms.Schema.collection schema)

end InfinitaryCombinatorics.Formalizations.FIMAD.CheckedZFC

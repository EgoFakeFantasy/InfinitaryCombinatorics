import Formalizations.FIMAD.SetTheorySentence

/-! The bounded unboundedness predicate in the same membership language as FI
MAD. This is an additional predicate; it does not replace internal infinitude,
which remains defined by absence of injections into internal natural numbers. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal
universe u

def Unbounded {U : Type u} (E : U → U → Prop) (w a : U) : Prop :=
  ∀ x, E x w → ∃ y, E y w ∧ (E x y ∨ x = y) ∧ E y a

def Difference {U : Type u} (E : U → U → Prop) (d a b : U) : Prop :=
  ∀ x, E x d ↔ E x a ∧ ¬ E x b

def UnboundedSplit {U : Type u} (E : U → U → Prop) (w a b : U) : Prop :=
  ∃ d e, Inter E d a b ∧ Difference E e a b ∧ Unbounded E w d ∧ Unbounded E w e

namespace Syntax
open YesMetaZFC YesMetaZFC.SetTheory Definitional.Project
open Definitional.Project.Formula
variable {M : SetTheory.Structure.{u}} {depth : Nat}

def UnboundedFormula (w a : Term depth) : Formula 1 depth :=
  .forallE (.imp (.mem (.bound 0) w.weaken)
    (.existsE (.conj (.mem (.bound 0) w.weaken.weaken)
      (.conj (.disj (.mem (.bound 1) (.bound 0))
        (Formula.extensionalEq (.bound 1) (.bound 0)))
        (.mem (.bound 0) a.weaken.weaken)))))

@[simp] theorem satisfies_UnboundedFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w a : Term depth) :
    Formula.satisfies env (UnboundedFormula w a) ↔
      Unbounded M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env a) := by
  simp only [UnboundedFormula, Unbounded, satisfies_forall_iff, satisfies_exists_iff,
    satisfies_imp_iff, satisfies_conj_iff, satisfies_disj_iff, satisfies_mem_iff,
    satisfies_extensionalEq_iff_eq hExt, Definitional.Term.eval_weaken]
  rfl

@[simp] theorem closed_UnboundedFormula (w a : Term depth)
    (hw : w.freeSupport = []) (ha : a.freeSupport = []) :
    (UnboundedFormula w a).FreeClosed := by
  simp only [UnboundedFormula, Definitional.Formula.FreeClosed,
    Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken,
    Definitional.Term.freeSupport_bound, hw, ha, and_self]
  all_goals trivial

def unboundedBody : Formula 1 2 := UnboundedFormula (.bound 1) (.bound 0)

theorem unboundedBody_closed : unboundedBody.FreeClosed :=
  closed_UnboundedFormula _ _ rfl rfl

end Syntax
end InfinitaryCombinatorics.Formalizations.FIMAD.Internal

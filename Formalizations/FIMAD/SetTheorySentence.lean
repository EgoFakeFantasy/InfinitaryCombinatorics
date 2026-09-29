import Formalizations.FIMAD.InternalSemantics

/-! A closed sentence expressing infinite FI MAD existence. Each syntax
constructor is checked against the separately stated membership semantics.
Equality atoms translate to native equality in extensional structures. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal
namespace Syntax
open YesMetaZFC
open YesMetaZFC.SetTheory
open Definitional.Project
open Definitional.Project.Formula
universe u
variable {M : SetTheory.Structure.{u}} {depth : Nat}

def SubsetFormula {depth : Nat} (a b : Term depth) : Formula 1 depth :=
  (.forallE (.imp (.mem (.bound 0) (a.weaken)) (.mem (.bound 0) (b.weaken))))

@[simp] theorem satisfies_SubsetFormula (_hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (a b : Term depth) :
    Formula.satisfies env (SubsetFormula a b) ↔ Subset M.mem (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [SubsetFormula, Subset, satisfies_mem_iff, satisfies_imp_iff, satisfies_forall_iff,
    Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_SubsetFormula (a b : Term depth) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (SubsetFormula a b : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, Definitional.Formula.FreeClosed, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ha, hb]
  all_goals trivial

def EmptyFormula {depth : Nat} (a : Term depth) : Formula 1 depth :=
  (.forallE (.neg (.mem (.bound 0) (a.weaken))))

@[simp] theorem satisfies_EmptyFormula (_hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (a : Term depth) :
    Formula.satisfies env (EmptyFormula a) ↔ Empty M.mem (Definitional.Term.eval env a) := by
  simp only [EmptyFormula, Empty, satisfies_mem_iff, satisfies_neg_iff, satisfies_forall_iff,
    Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_EmptyFormula (a : Term depth) (ha : a.freeSupport = []) :
    (EmptyFormula a : Formula 1 depth).FreeClosed := by
  simp only [EmptyFormula, Definitional.Formula.FreeClosed, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ha]
  all_goals trivial

def NonemptyFormula {depth : Nat} (a : Term depth) : Formula 1 depth :=
  (.existsE (.mem (.bound 0) (a.weaken)))

@[simp] theorem satisfies_NonemptyFormula (_hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (a : Term depth) :
    Formula.satisfies env (NonemptyFormula a) ↔ Nonempty M.mem (Definitional.Term.eval env a) := by
  simp only [NonemptyFormula, Nonempty, satisfies_mem_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_NonemptyFormula (a : Term depth) (ha : a.freeSupport = []) :
    (NonemptyFormula a : Formula 1 depth).FreeClosed := by
  simp only [NonemptyFormula, Definitional.Formula.FreeClosed, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ha]
  all_goals trivial

def InterFormula {depth : Nat} (d a b : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (d.weaken)) (.conj (.mem (.bound 0) (a.weaken)) (.mem (.bound 0) (b.weaken)))))

@[simp] theorem satisfies_InterFormula (_hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (d a b : Term depth) :
    Formula.satisfies env (InterFormula d a b) ↔ Inter M.mem (Definitional.Term.eval env d) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [InterFormula, Inter, satisfies_mem_iff, satisfies_conj_iff, satisfies_iff_iff,
    satisfies_forall_iff, Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_InterFormula (d a b : Term depth) (hd : d.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (InterFormula d a b : Formula 1 depth).FreeClosed := by
  simp only [InterFormula, Definitional.Formula.FreeClosed, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hd, ha, hb]
  all_goals trivial

def SuccFormula {depth : Nat} (b a : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (b.weaken)) (.disj (.mem (.bound 0) (a.weaken)) (Formula.extensionalEq (.bound 0) (a.weaken)))))

@[simp] theorem satisfies_SuccFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (b a : Term depth) :
    Formula.satisfies env (SuccFormula b a) ↔ Succ M.mem (Definitional.Term.eval env b) (Definitional.Term.eval env a) := by
  simp only [SuccFormula, Succ, satisfies_mem_iff, satisfies_disj_iff, satisfies_iff_iff,
    satisfies_forall_iff, satisfies_extensionalEq_iff_eq hExt, Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_SuccFormula (b a : Term depth) (hb : b.freeSupport = []) (ha : a.freeSupport = []) :
    (SuccFormula b a : Formula 1 depth).FreeClosed := by
  simp only [SuccFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hb, ha]
  all_goals trivial

def InductiveFormula {depth : Nat} (a : Term depth) : Formula 1 depth :=
  (.conj (.existsE (.conj (EmptyFormula (.bound 0)) (.mem (.bound 0) (a.weaken)))) (.forallE (.imp (.mem (.bound 0) (a.weaken)) (.existsE (.conj (SuccFormula (.bound 0) (.bound 1)) (.mem (.bound 0) (a.weaken.weaken)))))))

@[simp] theorem satisfies_InductiveFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (a : Term depth) :
    Formula.satisfies env (InductiveFormula a) ↔ Inductive M.mem (Definitional.Term.eval env a) := by
  simp only [InductiveFormula, Inductive, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_exists_iff, Definitional.Term.eval_weaken, satisfies_EmptyFormula hExt,
    satisfies_SuccFormula hExt]
  all_goals rfl

@[simp] theorem closed_InductiveFormula (a : Term depth) (ha : a.freeSupport = []) :
    (InductiveFormula a : Formula 1 depth).FreeClosed := by
  simp only [EmptyFormula, SuccFormula, InductiveFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ha]
  all_goals trivial

def OmegaFormula {depth : Nat} (w : Term depth) : Formula 1 depth :=
  (.conj (InductiveFormula (w)) (.forallE (.imp (InductiveFormula (.bound 0)) (SubsetFormula (w.weaken) (.bound 0)))))

@[simp] theorem satisfies_OmegaFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w : Term depth) :
    Formula.satisfies env (OmegaFormula w) ↔ Omega M.mem (Definitional.Term.eval env w) := by
  simp only [OmegaFormula, Omega, satisfies_conj_iff, satisfies_imp_iff, satisfies_forall_iff,
    Definitional.Term.eval_weaken, satisfies_InductiveFormula hExt, satisfies_SubsetFormula hExt]
  all_goals rfl

@[simp] theorem closed_OmegaFormula (w : Term depth) (hw : w.freeSupport = []) :
    (OmegaFormula w : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, EmptyFormula, SuccFormula, InductiveFormula, OmegaFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw]
  all_goals trivial

def SingletonFormula {depth : Nat} (s a : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (s.weaken)) (Formula.extensionalEq (.bound 0) (a.weaken))))

@[simp] theorem satisfies_SingletonFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (s a : Term depth) :
    Formula.satisfies env (SingletonFormula s a) ↔ Singleton M.mem (Definitional.Term.eval env s) (Definitional.Term.eval env a) := by
  simp only [SingletonFormula, Singleton, satisfies_mem_iff, satisfies_iff_iff, satisfies_forall_iff,
    satisfies_extensionalEq_iff_eq hExt, Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_SingletonFormula (s a : Term depth) (hs : s.freeSupport = []) (ha : a.freeSupport = []) :
    (SingletonFormula s a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hs, ha]
  all_goals trivial

def UnorderedPairFormula {depth : Nat} (s a b : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (s.weaken)) (.disj (Formula.extensionalEq (.bound 0) (a.weaken)) (Formula.extensionalEq (.bound 0) (b.weaken)))))

@[simp] theorem satisfies_UnorderedPairFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (s a b : Term depth) :
    Formula.satisfies env (UnorderedPairFormula s a b) ↔ UnorderedPair M.mem (Definitional.Term.eval env s) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [UnorderedPairFormula, UnorderedPair, satisfies_mem_iff, satisfies_disj_iff, satisfies_iff_iff,
    satisfies_forall_iff, satisfies_extensionalEq_iff_eq hExt, Definitional.Term.eval_weaken]
  all_goals rfl

@[simp] theorem closed_UnorderedPairFormula (s a b : Term depth) (hs : s.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (UnorderedPairFormula s a b : Formula 1 depth).FreeClosed := by
  simp only [UnorderedPairFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hs, ha, hb]
  all_goals trivial

def PairFormula {depth : Nat} (p a b : Term depth) : Formula 1 depth :=
  (.existsE (.existsE (.conj (SingletonFormula (.bound 1) (a.weaken.weaken)) (.conj (UnorderedPairFormula (.bound 0) (a.weaken.weaken) (b.weaken.weaken)) (UnorderedPairFormula (p.weaken.weaken) (.bound 1) (.bound 0))))))

@[simp] theorem satisfies_PairFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (p a b : Term depth) :
    Formula.satisfies env (PairFormula p a b) ↔ Pair M.mem (Definitional.Term.eval env p) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [PairFormula, Pair, satisfies_conj_iff, satisfies_exists_iff, Definitional.Term.eval_weaken,
    satisfies_SingletonFormula hExt, satisfies_UnorderedPairFormula hExt]
  all_goals rfl

@[simp] theorem closed_PairFormula (p a b : Term depth) (hp : p.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (PairFormula p a b : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hp, ha, hb]
  all_goals trivial

def ValueFormula {depth : Nat} (f a b : Term depth) : Formula 1 depth :=
  (.existsE (.conj (.mem (.bound 0) (f.weaken)) (PairFormula (.bound 0) (a.weaken) (b.weaken))))

@[simp] theorem satisfies_ValueFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (f a b : Term depth) :
    Formula.satisfies env (ValueFormula f a b) ↔ Value M.mem (Definitional.Term.eval env f) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [ValueFormula, Value, satisfies_mem_iff, satisfies_conj_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken, satisfies_PairFormula hExt]
  all_goals rfl

@[simp] theorem closed_ValueFormula (f a b : Term depth) (hf : f.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (ValueFormula f a b : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hf, ha, hb]
  all_goals trivial

def FunctionOnFormula {depth : Nat} (f a : Term depth) : Formula 1 depth :=
  (.conj (.forallE (.imp (.mem (.bound 0) (f.weaken)) (.existsE (.existsE (.conj (.mem (.bound 1) (a.weaken.weaken.weaken)) (PairFormula (.bound 2) (.bound 1) (.bound 0))))))) (.forallE (.imp (.mem (.bound 0) (a.weaken)) (.existsE (.conj (ValueFormula (f.weaken.weaken) (.bound 1) (.bound 0)) (.forallE (.imp (ValueFormula (f.weaken.weaken.weaken) (.bound 2) (.bound 0)) (Formula.extensionalEq (.bound 0) (.bound 1)))))))))

@[simp] theorem satisfies_FunctionOnFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (f a : Term depth) :
    Formula.satisfies env (FunctionOnFormula f a) ↔ FunctionOn M.mem (Definitional.Term.eval env f) (Definitional.Term.eval env a) := by
  simp only [FunctionOnFormula, FunctionOn, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_exists_iff, satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_weaken, satisfies_PairFormula hExt, satisfies_ValueFormula hExt]
  all_goals rfl

@[simp] theorem closed_FunctionOnFormula (f a : Term depth) (hf : f.freeSupport = []) (ha : a.freeSupport = []) :
    (FunctionOnFormula f a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hf, ha]
  all_goals trivial

def InjectionFormula {depth : Nat} (f a b : Term depth) : Formula 1 depth :=
  (.conj (FunctionOnFormula (f) (a)) (.conj (.forallE (.forallE (.imp (ValueFormula (f.weaken.weaken) (.bound 1) (.bound 0)) (.mem (.bound 0) (b.weaken.weaken))))) (.forallE (.forallE (.forallE (.imp (ValueFormula (f.weaken.weaken.weaken) (.bound 2) (.bound 0)) (.imp (ValueFormula (f.weaken.weaken.weaken) (.bound 1) (.bound 0)) (Formula.extensionalEq (.bound 2) (.bound 1)))))))))

@[simp] theorem satisfies_InjectionFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (f a b : Term depth) :
    Formula.satisfies env (InjectionFormula f a b) ↔ Injection M.mem (Definitional.Term.eval env f) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [InjectionFormula, Injection, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_extensionalEq_iff_eq hExt, Definitional.Term.eval_weaken,
    satisfies_FunctionOnFormula hExt, satisfies_ValueFormula hExt]
  all_goals rfl

@[simp] theorem closed_InjectionFormula (f a b : Term depth) (hf : f.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (InjectionFormula f a b : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hf, ha, hb]
  all_goals trivial

def FiniteFormula {depth : Nat} (w a : Term depth) : Formula 1 depth :=
  (.existsE (.conj (.mem (.bound 0) (w.weaken)) (.existsE (InjectionFormula (.bound 0) (a.weaken.weaken) (.bound 1)))))

@[simp] theorem satisfies_FiniteFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w a : Term depth) :
    Formula.satisfies env (FiniteFormula w a) ↔ Finite M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env a) := by
  simp only [FiniteFormula, Finite, satisfies_mem_iff, satisfies_conj_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken, satisfies_InjectionFormula hExt]
  all_goals rfl

@[simp] theorem closed_FiniteFormula (w a : Term depth) (hw : w.freeSupport = []) (ha : a.freeSupport = []) :
    (FiniteFormula w a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, ha]
  all_goals trivial

def InfiniteFormula {depth : Nat} (w a : Term depth) : Formula 1 depth :=
  (.neg (FiniteFormula (w) (a)))

@[simp] theorem satisfies_InfiniteFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w a : Term depth) :
    Formula.satisfies env (InfiniteFormula w a) ↔ Infinite M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env a) := by
  simp only [InfiniteFormula, Infinite, satisfies_neg_iff, satisfies_FiniteFormula hExt]
  all_goals rfl

@[simp] theorem closed_InfiniteFormula (w a : Term depth) (hw : w.freeSupport = []) (ha : a.freeSupport = []) :
    (InfiniteFormula w a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, ha]
  all_goals trivial

def InfiniteInterFormula {depth : Nat} (w a b : Term depth) : Formula 1 depth :=
  (.existsE (.conj (InterFormula (.bound 0) (a.weaken) (b.weaken)) (InfiniteFormula (w.weaken) (.bound 0))))

@[simp] theorem satisfies_InfiniteInterFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w a b : Term depth) :
    Formula.satisfies env (InfiniteInterFormula w a b) ↔ InfiniteInter M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env a) (Definitional.Term.eval env b) := by
  simp only [InfiniteInterFormula, InfiniteInter, satisfies_conj_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken, satisfies_InterFormula hExt, satisfies_InfiniteFormula hExt]
  all_goals rfl

@[simp] theorem closed_InfiniteInterFormula (w a b : Term depth) (hw : w.freeSupport = []) (ha : a.freeSupport = []) (hb : b.freeSupport = []) :
    (InfiniteInterFormula w a b : Formula 1 depth).FreeClosed := by
  simp only [InterFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, InfiniteInterFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, ha, hb]
  all_goals trivial

def ADFormula {depth : Nat} (w A : Term depth) : Formula 1 depth :=
  (.conj (InfiniteFormula (w) (A)) (.conj (.forallE (.imp (.mem (.bound 0) (A.weaken)) (.conj (SubsetFormula (.bound 0) (w.weaken)) (InfiniteFormula (w.weaken) (.bound 0))))) (.forallE (.forallE (.imp (.mem (.bound 1) (A.weaken.weaken)) (.imp (.mem (.bound 0) (A.weaken.weaken)) (.imp (.neg (Formula.extensionalEq (.bound 1) (.bound 0))) (.existsE (.conj (InterFormula (.bound 0) (.bound 2) (.bound 1)) (FiniteFormula (w.weaken.weaken.weaken) (.bound 0)))))))))))

@[simp] theorem satisfies_ADFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w A : Term depth) :
    Formula.satisfies env (ADFormula w A) ↔ AD M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env A) := by
  simp only [ADFormula, AD, satisfies_mem_iff, satisfies_neg_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_exists_iff, satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_weaken, satisfies_InfiniteFormula hExt, satisfies_SubsetFormula hExt,
    satisfies_InterFormula hExt, satisfies_FiniteFormula hExt]
  all_goals rfl

@[simp] theorem closed_ADFormula (w A : Term depth) (hw : w.freeSupport = []) (hA : A.freeSupport = []) :
    (ADFormula w A : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, InterFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, ADFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, hA]
  all_goals trivial

def MADFormula {depth : Nat} (w A : Term depth) : Formula 1 depth :=
  (.conj (ADFormula (w) (A)) (.forallE (.imp (SubsetFormula (.bound 0) (w.weaken)) (.imp (InfiniteFormula (w.weaken) (.bound 0)) (.existsE (.conj (.mem (.bound 0) (A.weaken.weaken)) (InfiniteInterFormula (w.weaken.weaken) (.bound 1) (.bound 0))))))))

@[simp] theorem satisfies_MADFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w A : Term depth) :
    Formula.satisfies env (MADFormula w A) ↔ MAD M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env A) := by
  simp only [MADFormula, MAD, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_forall_iff, satisfies_exists_iff, Definitional.Term.eval_weaken, satisfies_ADFormula hExt,
    satisfies_SubsetFormula hExt, satisfies_InfiniteFormula hExt, satisfies_InfiniteInterFormula hExt]
  all_goals rfl

@[simp] theorem closed_MADFormula (w A : Term depth) (hw : w.freeSupport = []) (hA : A.freeSupport = []) :
    (MADFormula w A : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, InterFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, InfiniteInterFormula, ADFormula, MADFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, hA]
  all_goals trivial

def FinSequenceFormula {depth : Nat} (w C : Term depth) : Formula 1 depth :=
  (.conj (FunctionOnFormula (C) (w)) (.conj (.forallE (.forallE (.imp (.mem (.bound 1) (w.weaken.weaken)) (.imp (ValueFormula (C.weaken.weaken) (.bound 1) (.bound 0)) (.conj (SubsetFormula (.bound 0) (w.weaken.weaken)) (.conj (FiniteFormula (w.weaken.weaken) (.bound 0)) (NonemptyFormula (.bound 0)))))))) (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (w.weaken.weaken.weaken.weaken)) (.imp (.mem (.bound 2) (w.weaken.weaken.weaken.weaken)) (.imp (.neg (Formula.extensionalEq (.bound 3) (.bound 2))) (.imp (ValueFormula (C.weaken.weaken.weaken.weaken) (.bound 3) (.bound 1)) (.imp (ValueFormula (C.weaken.weaken.weaken.weaken) (.bound 2) (.bound 0)) (.neg (.existsE (.conj (.mem (.bound 0) (.bound 2)) (.mem (.bound 0) (.bound 1))))))))))))))))

@[simp] theorem satisfies_FinSequenceFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w C : Term depth) :
    Formula.satisfies env (FinSequenceFormula w C) ↔ FinSequence M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env C) := by
  simp only [FinSequenceFormula, FinSequence, satisfies_mem_iff, satisfies_neg_iff, satisfies_conj_iff,
    satisfies_imp_iff, satisfies_forall_iff, satisfies_exists_iff, satisfies_extensionalEq_iff_eq hExt,
    Definitional.Term.eval_weaken, satisfies_FunctionOnFormula hExt, satisfies_ValueFormula hExt,
    satisfies_SubsetFormula hExt, satisfies_FiniteFormula hExt, satisfies_NonemptyFormula hExt]
  all_goals rfl

@[simp] theorem closed_FinSequenceFormula (w C : Term depth) (hw : w.freeSupport = []) (hC : C.freeSupport = []) :
    (FinSequenceFormula w C : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, NonemptyFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, FinSequenceFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, hC]
  all_goals trivial

def TraceAtFormula {depth : Nat} (C a n : Term depth) : Formula 1 depth :=
  (.existsE (.conj (ValueFormula (C.weaken) (n.weaken) (.bound 0)) (.existsE (.conj (.mem (.bound 0) (a.weaken.weaken)) (.mem (.bound 0) (.bound 1))))))

@[simp] theorem satisfies_TraceAtFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (C a n : Term depth) :
    Formula.satisfies env (TraceAtFormula C a n) ↔ TraceAt M.mem (Definitional.Term.eval env C) (Definitional.Term.eval env a) (Definitional.Term.eval env n) := by
  simp only [TraceAtFormula, TraceAt, satisfies_mem_iff, satisfies_conj_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken, satisfies_ValueFormula hExt]
  all_goals rfl

@[simp] theorem closed_TraceAtFormula (C a n : Term depth) (hC : C.freeSupport = []) (ha : a.freeSupport = []) (hn : n.freeSupport = []) :
    (TraceAtFormula C a n : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, TraceAtFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hC, ha, hn]
  all_goals trivial

def RestrictedTraceFormula {depth : Nat} (t C I a : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (t.weaken)) (.conj (.mem (.bound 0) (I.weaken)) (TraceAtFormula (C.weaken) (a.weaken) (.bound 0)))))

@[simp] theorem satisfies_RestrictedTraceFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (t C I a : Term depth) :
    Formula.satisfies env (RestrictedTraceFormula t C I a) ↔ RestrictedTrace M.mem (Definitional.Term.eval env t) (Definitional.Term.eval env C) (Definitional.Term.eval env I) (Definitional.Term.eval env a) := by
  simp only [RestrictedTraceFormula, RestrictedTrace, satisfies_mem_iff, satisfies_conj_iff,
    satisfies_iff_iff, satisfies_forall_iff, Definitional.Term.eval_weaken, satisfies_TraceAtFormula hExt]
  all_goals rfl

@[simp] theorem closed_RestrictedTraceFormula (t C I a : Term depth) (ht : t.freeSupport = []) (hC : C.freeSupport = []) (hI : I.freeSupport = []) (ha : a.freeSupport = []) :
    (RestrictedTraceFormula t C I a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, TraceAtFormula, RestrictedTraceFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ht, hC, hI, ha]
  all_goals trivial

def RetainedFormula {depth : Nat} (w C I a : Term depth) : Formula 1 depth :=
  (.existsE (.conj (RestrictedTraceFormula (.bound 0) (C.weaken) (I.weaken) (a.weaken)) (InfiniteFormula (w.weaken) (.bound 0))))

@[simp] theorem satisfies_RetainedFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w C I a : Term depth) :
    Formula.satisfies env (RetainedFormula w C I a) ↔ Retained M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env C) (Definitional.Term.eval env I) (Definitional.Term.eval env a) := by
  simp only [RetainedFormula, Retained, satisfies_conj_iff, satisfies_exists_iff,
    Definitional.Term.eval_weaken, satisfies_RestrictedTraceFormula hExt, satisfies_InfiniteFormula hExt]
  all_goals rfl

@[simp] theorem closed_RetainedFormula (w C I a : Term depth) (hw : w.freeSupport = []) (hC : C.freeSupport = []) (hI : I.freeSupport = []) (ha : a.freeSupport = []) :
    (RetainedFormula w C I a : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, TraceAtFormula, RestrictedTraceFormula, RetainedFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, hC, hI, ha]
  all_goals trivial

def CommonTraceFormula {depth : Nat} (t C I F : Term depth) : Formula 1 depth :=
  (.forallE (.iff (.mem (.bound 0) (t.weaken)) (.conj (.mem (.bound 0) (I.weaken)) (.forallE (.imp (.mem (.bound 0) (F.weaken.weaken)) (TraceAtFormula (C.weaken.weaken) (.bound 0) (.bound 1)))))))

@[simp] theorem satisfies_CommonTraceFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (t C I F : Term depth) :
    Formula.satisfies env (CommonTraceFormula t C I F) ↔ CommonTrace M.mem (Definitional.Term.eval env t) (Definitional.Term.eval env C) (Definitional.Term.eval env I) (Definitional.Term.eval env F) := by
  simp only [CommonTraceFormula, CommonTrace, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff,
    satisfies_iff_iff, satisfies_forall_iff, Definitional.Term.eval_weaken, satisfies_TraceAtFormula hExt]
  all_goals rfl

@[simp] theorem closed_CommonTraceFormula (t C I F : Term depth) (ht : t.freeSupport = []) (hC : C.freeSupport = []) (hI : I.freeSupport = []) (hF : F.freeSupport = []) :
    (CommonTraceFormula t C I F : Formula 1 depth).FreeClosed := by
  simp only [SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, TraceAtFormula, CommonTraceFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, ht, hC, hI, hF]
  all_goals trivial

def FIFormula {depth : Nat} (w A : Term depth) : Formula 1 depth :=
  (.forallE (.imp (FinSequenceFormula (w.weaken) (.bound 0)) (.existsE (.conj (SubsetFormula (.bound 0) (w.weaken.weaken)) (.conj (InfiniteFormula (w.weaken.weaken) (.bound 0)) (.forallE (.imp (SubsetFormula (.bound 0) (A.weaken.weaken.weaken)) (.imp (FiniteFormula (w.weaken.weaken.weaken) (.bound 0)) (.imp (NonemptyFormula (.bound 0)) (.imp (.forallE (.imp (.mem (.bound 0) (.bound 1)) (RetainedFormula (w.weaken.weaken.weaken.weaken) (.bound 3) (.bound 2) (.bound 0)))) (.existsE (.conj (CommonTraceFormula (.bound 0) (.bound 3) (.bound 2) (.bound 1)) (InfiniteFormula (w.weaken.weaken.weaken.weaken) (.bound 0))))))))))))))

@[simp] theorem satisfies_FIFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) (w A : Term depth) :
    Formula.satisfies env (FIFormula w A) ↔ FI M.mem (Definitional.Term.eval env w) (Definitional.Term.eval env A) := by
  simp only [FIFormula, FI, satisfies_mem_iff, satisfies_conj_iff, satisfies_imp_iff, satisfies_forall_iff,
    satisfies_exists_iff, Definitional.Term.eval_weaken, satisfies_FinSequenceFormula hExt,
    satisfies_SubsetFormula hExt, satisfies_InfiniteFormula hExt, satisfies_FiniteFormula hExt,
    satisfies_NonemptyFormula hExt, satisfies_RetainedFormula hExt, satisfies_CommonTraceFormula hExt]
  all_goals rfl

@[simp] theorem closed_FIFormula (w A : Term depth) (hw : w.freeSupport = []) (hA : A.freeSupport = []) :
    (FIFormula w A : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, NonemptyFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, FinSequenceFormula, TraceAtFormula, RestrictedTraceFormula, RetainedFormula, CommonTraceFormula, FIFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self, hw, hA]
  all_goals trivial

def ExistsFIMADFormula {depth : Nat} : Formula 1 depth :=
  (.existsE (.existsE (.conj (OmegaFormula (.bound 1)) (.conj (MADFormula (.bound 1) (.bound 0)) (FIFormula (.bound 1) (.bound 0))))))

@[simp] theorem satisfies_ExistsFIMADFormula (hExt : SetTheory.Extensional M)
    (env : SetTheory.Env M depth) :
    Formula.satisfies env (ExistsFIMADFormula ) ↔ ExistsFIMAD M.mem  := by
  simp only [ExistsFIMADFormula, ExistsFIMAD, satisfies_conj_iff, satisfies_exists_iff,
    satisfies_OmegaFormula hExt, satisfies_MADFormula hExt, satisfies_FIFormula hExt]
  all_goals rfl

@[simp] theorem closed_ExistsFIMADFormula  :
    (ExistsFIMADFormula  : Formula 1 depth).FreeClosed := by
  simp only [SubsetFormula, EmptyFormula, NonemptyFormula, InterFormula, SuccFormula, InductiveFormula, OmegaFormula, SingletonFormula, UnorderedPairFormula, PairFormula, ValueFormula, FunctionOnFormula, InjectionFormula, FiniteFormula, InfiniteFormula, InfiniteInterFormula, ADFormula, MADFormula, FinSequenceFormula, TraceAtFormula, RestrictedTraceFormula, RetainedFormula, CommonTraceFormula, FIFormula, ExistsFIMADFormula, Definitional.Formula.FreeClosed, Formula.extensionalEq_freeClosed_iff, Definitional.Term.freeSupport_weaken, Definitional.Term.freeSupport_bound, and_self]
  all_goals trivial

def sentence : Sentence :=
  Sentence.ofFormula (ExistsFIMADFormula (depth := 0)) (closed_ExistsFIMADFormula)

theorem sentence_semantics (hExt : SetTheory.Extensional M) :
    M.SatisfiesSentence sentence ↔ ExistsFIMAD M.mem := by
  rw [SetTheory.Structure.satisfiesSentence_iff]
  simp only [sentence, Sentence.ofFormula, satisfies_ExistsFIMADFormula hExt]
  constructor
  · intro h
    letI := M.nonempty
    exact h (fun _ => Classical.choice M.nonempty)
  · exact fun h _ => h

end Syntax
end InfinitaryCombinatorics.Formalizations.FIMAD.Internal

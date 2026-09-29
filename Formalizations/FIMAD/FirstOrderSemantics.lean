import Formalizations.FIMAD.SetTheorySentence

/-! Semantics of the actual pure first-order translation. This connects
the project's depth-indexed formulas to the public YesMetaZFC proof kernel. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal

theorem Syntax.sentence_is_firstOrder :
    YesMetaZFC.Logic.FirstOrder.Formula.Sentence
      (YesMetaZFC.SetTheory.Definitional.Project.fo_sentence Syntax.sentence) :=
  YesMetaZFC.SetTheory.Definitional.Project.fo_sentence_sentence Syntax.sentence

namespace FirstOrderBridge
open YesMetaZFC YesMetaZFC.SetTheory
open Definitional.Project
universe u

def toFirstOrder (M : SetTheory.Structure.{u}) : Logic.FirstOrder.Structure signature where
  Domain := M.Domain
  nonempty := M.nonempty
  sortInterp := fun _ _ => True
  sortNonempty := fun _ => M.nonempty.elim fun x => ⟨x, trivial⟩
  funcInterp := fun f => nomatch f
  funcSort := fun f => nomatch f
  relInterp := fun _ xs => match xs with
    | [x, y] => M.mem x y
    | _ => False

def restrict {M : SetTheory.Structure.{u}}
    (env : Logic.FirstOrder.Env (toFirstOrder M)) (depth : Nat) : SetTheory.Env M depth where
  bound := fun i => env.boundVal SetSort.set i.val
  free := env.freeVal SetSort.set

theorem restrict_push {M : SetTheory.Structure.{u}}
    (env : Logic.FirstOrder.Env (toFirstOrder M)) (depth : Nat) (x : M.Domain) :
    restrict (env.pushBound SetSort.set x trivial) (depth + 1) =
      (restrict env depth).push x := by
  rw [SetTheory.Env.mk.injEq]
  constructor
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [restrict, Logic.FirstOrder.Env.pushBound, SetTheory.Env.push]
  · rfl

theorem eval_term {M : SetTheory.Structure.{u}}
    (env : Logic.FirstOrder.Env (toFirstOrder M)) {depth : Nat} (t : Term depth) :
    Logic.FirstOrder.Term.eval env (fo_term t) =
      Definitional.Term.eval (restrict env depth) t := by
  cases t <;> simp [fo_term, Logic.FirstOrder.Term.eval, Definitional.Term.eval, restrict]

theorem satisfies_formula {M : SetTheory.Structure.{u}} (hExt : Extensional M)
    {depth : Nat} (φ : Formula 1 depth)
    (env : Logic.FirstOrder.Env (toFirstOrder M)) :
    Logic.FirstOrder.Formula.satisfies env (fo_formula φ) ↔
      Formula.satisfies (restrict env depth) φ := by
  induction φ generalizing env with
  | falsum => simp [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_falsum_iff]
  | truth => simp [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_truth_iff]
  | mem a b =>
    simp only [fo_formula, fo_mem, Logic.FirstOrder.Formula.satisfies, List.map_cons, List.map_nil]
    change M.mem (Logic.FirstOrder.Term.eval env (fo_term a))
        (Logic.FirstOrder.Term.eval env (fo_term b)) ↔ _
    rw [eval_term, eval_term, Formula.satisfies_mem_iff]
  | atom symbol level args =>
    cases symbol with
    | extensionalEq =>
      simp only [fo_formula, Logic.FirstOrder.Formula.satisfies,
        Formula.satisfies_atom_extensionalEq_iff, eval_term]
      exact ⟨fun h x => h ▸ Iff.rfl, hExt.eq_of_same_members _ _⟩
    | subset =>
      simp only [fo_formula, fo_mem, Logic.FirstOrder.Formula.satisfies,
        List.map_cons, List.map_nil, eval_term, restrict_push,
        Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
        Formula.satisfies_atom_subset_iff]
      change (∀ x, True → (M.mem x _ → M.mem x _)) ↔ (∀ x, M.mem x _ → M.mem x _)
      simp only [true_implies]
  | neg φ ih =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_neg_iff]
    exact not_congr (ih env)
  | conj φ ψ ihφ ihψ =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_conj_iff]
    exact and_congr (ihφ env) (ihψ env)
  | disj φ ψ ihφ ihψ =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_disj_iff]
    exact or_congr (ihφ env) (ihψ env)
  | imp φ ψ ihφ ihψ =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_imp_iff]
    exact imp_congr (ihφ env) (ihψ env)
  | iff φ ψ ihφ ihψ =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies, Formula.satisfies_iff_iff]
    exact iff_congr (ihφ env) (ihψ env)
  | forallE φ ih =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies]
    change (∀ x, ∀ hx : True, Logic.FirstOrder.Formula.satisfies
      (env.pushBound SetSort.set x hx) (fo_formula φ)) ↔ _
    simp only [ih, restrict_push, Formula.satisfies_forall_iff, true_implies]
    rfl
  | existsE φ ih =>
    simp only [fo_formula, Logic.FirstOrder.Formula.satisfies]
    change (∃ x, ∃ hx : True, Logic.FirstOrder.Formula.satisfies
      (env.pushBound SetSort.set x hx) (fo_formula φ)) ↔ _
    simp only [ih, restrict_push, Formula.satisfies_exists_iff, exists_true_left]
    rfl

/-- The concrete sentence used by the first-order proof kernel expresses E. -/
theorem satisfies_fimad_sentence {M : SetTheory.Structure.{u}} (hExt : Extensional M)
    (env : Logic.FirstOrder.Env (toFirstOrder M)) :
    Logic.FirstOrder.Formula.satisfies env (fo_sentence Syntax.sentence) ↔
      ExistsFIMAD M.mem := by
  rw [fo_sentence, satisfies_formula hExt]
  exact Syntax.satisfies_ExistsFIMADFormula hExt _

end FirstOrderBridge
end InfinitaryCombinatorics.Formalizations.FIMAD.Internal

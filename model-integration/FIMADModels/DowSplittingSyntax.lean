import FIMADModels.DowNameSplitting

/-! Splitting in the same membership language and with the same internal
infinitude predicate as the FI MAD sentence. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def differenceFormula {n} (d X b : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem .newest d.weaken)
    (.conj (.mem .newest X.weaken) (.neg (.mem .newest b.weaken))))

def splitsSetFormula {n} (w X b : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (Internal.Syntax.InterFormula (.bound 1) X.weaken.weaken b.weaken.weaken)
    (.conj (differenceFormula .newest X.weaken.weaken b.weaken.weaken)
      (.conj (Internal.Syntax.InfiniteFormula w.weaken.weaken (.bound 1))
        (Internal.Syntax.InfiniteFormula w.weaken.weaken .newest)))))

def splitsTestsFormula {n} (w b H : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest H.weaken) (.imp (Internal.Syntax.InfiniteFormula w.weaken .newest)
    (splitsSetFormula w.weaken .newest b.weaken)))

derive_free_closed differenceFormula
derive_free_closed splitsSetFormula
derive_free_closed splitsTestsFormula

theorem differenceFormula_semantics {n} (ρ : Env M n) (d X b : Project.Term n) :
    Project.Formula.satisfies ρ (differenceFormula d X b) ↔
      Internal.Difference M.mem (d.eval ρ) (X.eval ρ) (b.eval ρ) := by
  simp only [differenceFormula, Internal.Difference, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem splitsSetFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w X b : Project.Term n) : Project.Formula.satisfies ρ (splitsSetFormula w X b) ↔
      SplitsSet (w.eval ρ) (X.eval ρ) (b.eval ρ) := by
  simp only [splitsSetFormula, SplitsSet, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Internal.Syntax.satisfies_InterFormula hE,
    differenceFormula_semantics, Internal.Syntax.satisfies_InfiniteFormula hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem splitsTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w b H : Project.Term n) : Project.Formula.satisfies ρ (splitsTestsFormula w b H) ↔
      SplitsTests (w.eval ρ) (b.eval ρ) (H.eval ρ) := by
  simp only [splitsTestsFormula, SplitsTests, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_InfiniteFormula hE, splitsSetFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax
end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

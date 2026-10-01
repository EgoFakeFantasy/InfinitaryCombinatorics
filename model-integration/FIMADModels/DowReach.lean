import FIMADModels.DowAmalgamation

/-! The internal least dense-stem closure used in Dow's preservation proof.
It is defined by intersection of all closed subsets, rather than by a host
inductive type indexed by standard natural numbers or external ordinals. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def DenseConditions (w A D : M.Domain) : Prop :=
  ∀ p, CodedCondition w A p →
    ∃ q, M.mem q D ∧ CodedCondition w A q ∧ CodedExtends (M := M) q p

def ReachReady (w a s H : M.Domain) : Prop :=
  ∀ n, M.mem n w → ∃ t r, Tail w a n t ∧ M.IsUnionOfTwo r s t ∧ M.mem r H

def ReachClosed (w A D H : M.Domain) : Prop :=
  (∀ s, M.mem s H → FiniteSubset w s) ∧
  (∀ s p, M.mem p D → SameStem w A s p → M.mem s H) ∧
  ∀ s a, FiniteSubset w s → M.mem a A → ReachReady w a s H → M.mem s H

namespace Syntax
def denseConditionsFormula {n} (w A D : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (codedConditionFormula w.weaken A.weaken .newest)
    (.existsE (.conj (.mem .newest D.weaken.weaken)
      (.conj (codedConditionFormula w.weaken.weaken A.weaken.weaken .newest)
        (codedExtendsFormula .newest (.bound 1))))))

def reachReadyFormula {n} (w a s H : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest w.weaken)
    (.existsE (.existsE (.conj (tailFormula w.weaken.weaken.weaken
      a.weaken.weaken.weaken (.bound 2) (.bound 1))
      (.conj (Project.Formula.isUnionOfTwo .newest s.weaken.weaken.weaken (.bound 1))
        (.mem .newest H.weaken.weaken.weaken))))))

def reachClosedFormula {n} (w A D H : Project.Term n) : Project.Formula 1 n :=
  .conj (.forallE (.imp (.mem .newest H.weaken) (finiteSubsetFormula w.weaken .newest)))
    (.conj (.forallE (.forallE (.imp (.mem .newest D.weaken.weaken)
      (.imp (sameStemFormula w.weaken.weaken A.weaken.weaken (.bound 1) .newest)
        (.mem (.bound 1) H.weaken.weaken)))))
      (.forallE (.forallE (.imp (finiteSubsetFormula w.weaken.weaken (.bound 1))
        (.imp (.mem .newest A.weaken.weaken)
          (.imp (reachReadyFormula w.weaken.weaken .newest (.bound 1) H.weaken.weaken)
            (.mem (.bound 1) H.weaken.weaken)))))))

derive_free_closed denseConditionsFormula
derive_free_closed reachReadyFormula
derive_free_closed reachClosedFormula

theorem denseConditionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A D : Project.Term n) : Project.Formula.satisfies ρ (denseConditionsFormula w A D) ↔
      DenseConditions (w.eval ρ) (A.eval ρ) (D.eval ρ) := by
  simp only [denseConditionsFormula, DenseConditions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, codedConditionFormula_semantics hE,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, codedExtendsFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem reachReadyFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w a s H : Project.Term n) : Project.Formula.satisfies ρ (reachReadyFormula w a s H) ↔
      ReachReady (w.eval ρ) (a.eval ρ) (s.eval ρ) (H.eval ρ) := by
  simp only [reachReadyFormula, ReachReady, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    tailFormula_semantics hE, Project.Formula.satisfies_isUnionOfTwo_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem reachClosedFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A D H : Project.Term n) : Project.Formula.satisfies ρ (reachClosedFormula w A D H) ↔
      ReachClosed (w.eval ρ) (A.eval ρ) (D.eval ρ) (H.eval ρ) := by
  simp only [reachClosedFormula, ReachClosed, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, finiteSubsetFormula_semantics hE,
    sameStemFormula_semantics hE, reachReadyFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

/-- Closure implies admissibility of the set of reachable stems. -/
theorem reach_closed_admissible {w A D H : M.Domain}
    (hH : ReachClosed w A D H) : Admissible w A H := by
  intro s hs hsH a ha
  classical
  apply Classical.byContradiction
  intro hNoBound
  apply hsH
  apply hH.2.2 s a hs ha
  intro n hn
  apply Classical.byContradiction
  intro hNoTail
  apply hNoBound
  refine ⟨n, hn, fun t ht r hr hRH => ?_⟩
  exact hNoTail ⟨t, r, ht, hr, hRH⟩

theorem dense_reach_all (hZF : M.Models SetTheory.ZF) {w A D H : M.Domain}
    (hDense : DenseConditions w A D) (hH : ReachClosed w A D H) :
    ∀ s, FiniteSubset w s → M.mem s H := by
  intro s hs
  classical
  by_cases hsH : M.mem s H
  · exact hsH
  · let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
    obtain ⟨p, hp⟩ := I.total s H
    have hCond : Condition w A s H := ⟨hs, hH.1, hsH, reach_closed_admissible hH⟩
    obtain ⟨q, hqD, hqCond, hqp⟩ := hDense p ⟨s, H, hp, hCond⟩
    obtain ⟨t, T, hqt, ht⟩ := hqCond
    have htsH := extends_of_codes hZF hqt hp hqp
    exact False.elim (htsH.2.2 (hH.2.1 t q hqD ⟨T, hqt, ht⟩))

/-- Actual least closure set, with its induction principle over internal sets. -/
theorem least_reach_exists (hZF : M.Models SetTheory.ZF) (w A D : M.Domain) :
    ∃ R, ReachClosed w A D R ∧
      ∀ H, ReachClosed w A D H → Internal.Subset M.mem R H := by
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push D
  let φ : UnarySchema 3 := {
    body := .conj (Syntax.finiteSubsetFormula (.bound 3) .newest)
      (.forallE (.imp (Syntax.reachClosedFormula (.bound 4) (.bound 3) (.bound 2) .newest)
        (.mem (.bound 1) .newest))) }
  have hφ s : φ.denote ρ s ↔ FiniteSubset w s ∧
      ∀ H, ReachClosed w A D H → M.mem s H := by
    simp only [UnarySchema.denote, φ, Project.Formula.satisfies_conj_iff,
      Syntax.finiteSubsetFormula_semantics hZF.1, Project.Formula.satisfies_forall_iff,
      Project.Formula.satisfies_imp_iff, Syntax.reachClosedFormula_semantics hZF.1,
      Project.Formula.satisfies_mem_iff]
    rfl
  obtain ⟨R, hR⟩ := ZF.separation_exists_d hZF φ ρ W
  have hr s : M.mem s R ↔ FiniteSubset w s ∧
      ∀ H, ReachClosed w A D H → M.mem s H := by
    rw [hR s]
    change M.mem s W ∧ φ.denote ρ s ↔ _
    rw [hφ s]
    exact ⟨fun h => h.2, fun h => ⟨(hW s).mpr h.1.1, h⟩⟩
  have hMin H (hH : ReachClosed w A D H) : Internal.Subset M.mem R H :=
    fun s hs => ((hr s).mp hs).2 H hH
  refine ⟨R, ⟨fun s hs => ((hr s).mp hs).1, ?_, ?_⟩, hMin⟩
  · intro s p hp hStem
    exact (hr s).mpr ⟨hStem.elim fun S hS => hS.2.1,
      fun H hH => hH.2.1 s p hp hStem⟩
  · intro s a hs ha hReady
    refine (hr s).mpr ⟨hs, fun H hH => hH.2.2 s a hs ha ?_⟩
    intro n hn
    obtain ⟨t, r, ht, hrUnion, hrR⟩ := hReady n hn
    exact ⟨t, r, ht, hrUnion, hMin H hH r hrR⟩

namespace Syntax
def reachAllBody : Project.Formula 1 4 :=
  .imp (denseConditionsFormula (.bound 3) (.bound 2) (.bound 1))
    (.imp (reachClosedFormula (.bound 3) (.bound 2) (.bound 1) .newest)
      (.forallE (.imp (finiteSubsetFormula (.bound 4) .newest) (.mem .newest (.bound 1)))))

theorem reachAllBody_closed : reachAllBody.FreeClosed := by
  simp -implicitDefEqProofs [reachAllBody, Definitional.Formula.FreeClosed]

def reachAllSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose reachAllBody) (ObjectTheory.universalClose_closed _ reachAllBody_closed)

theorem reachAllBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 4) :
    Project.Formula.satisfies ρ reachAllBody := by
  simp only [reachAllBody, Project.Formula.satisfies_imp_iff,
    denseConditionsFormula_semantics hZF.1, reachClosedFormula_semantics hZF.1,
    Project.Formula.satisfies_forall_iff, finiteSubsetFormula_semantics hZF.1,
    Project.Formula.satisfies_mem_iff, Definitional.Term.eval_newest]
  exact fun hDense hH => dense_reach_all hZF hDense hH

def leastReachBody : Project.Formula 1 3 :=
  .existsE (.conj (reachClosedFormula (.bound 3) (.bound 2) (.bound 1) .newest)
    (.forallE (.imp (reachClosedFormula (.bound 4) (.bound 3) (.bound 2) .newest)
      (Internal.Syntax.SubsetFormula (.bound 1) .newest))))

theorem leastReachBody_closed : leastReachBody.FreeClosed := by
  simp -implicitDefEqProofs [leastReachBody, Definitional.Formula.FreeClosed]

def leastReachSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose leastReachBody)
  (ObjectTheory.universalClose_closed _ leastReachBody_closed)

theorem leastReachBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 3) :
    Project.Formula.satisfies ρ leastReachBody := by
  simp only [leastReachBody, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, reachClosedFormula_semantics hZF.1,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Internal.Syntax.satisfies_SubsetFormula hZF.1]
  exact least_reach_exists hZF (ρ.bound 2) (ρ.bound 1) (ρ.bound 0)
end Syntax

theorem derives_dense_reach : Project.Derives SetTheory.ZF Syntax.reachAllSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.reachAllBody (Syntax.reachAllBody_valid hZF)

theorem derives_least_reach : Project.Derives SetTheory.ZF Syntax.leastReachSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.leastReachBody (Syntax.leastReachBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

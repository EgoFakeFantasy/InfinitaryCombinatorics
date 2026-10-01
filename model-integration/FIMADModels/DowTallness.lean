import FIMADModels.DowTallTests

/-! The internal tallness test theorem for the exact Dow forcing. This is a
first-order theorem of ZFC about actual monotone, unbounded decision relations;
it does not assume that the ground model is externally well founded. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def TallDensity (w A E B : M.Domain) : Prop :=
  ∀ p N, CodedCondition w A p → M.mem N w → ∃ q k,
    CodedCondition w A q ∧ CodedExtends (M := M) q p ∧
      M.mem k B ∧ M.mem k w ∧ AtLeast (M := M) N k ∧ Entry_d M q k E

def TallTestsWitness (w A E H : M.Domain) : Prop :=
  InternalCountable w H ∧ (∀ X, M.mem X H → Internal.Subset M.mem X w) ∧
    ∀ B, MeetsTests w B H → TallDensity w A E B

theorem total_tests_tall (hZF : M.Models SetTheory.ZF) {w A E H : M.Domain}
    (hw : M.IsOmega w) (hTests : TotalTailTests w A E H) : TallTestsWitness w A E H := by
  classical
  have hw' := (Internal.omega_native_iff hZF.1 w).mpr hw
  refine ⟨hTests.1, hTests.2.1, ?_⟩
  intro B hB p N hp hN
  apply Classical.byContradiction
  intro hNo
  obtain ⟨s, S, hps, hCond⟩ := hp
  have hStem : SameStem w A s p := ⟨S, hps, hCond⟩
  have hAvoid : AvoidsTail w A E p B N := by
    intro k hkw hkB hNk q hq hqp hqk
    exact hNo ⟨q, k, hq, hqp, hkB, hkw, hNk, hqk⟩
  obtain ⟨V, hV, hVH⟩ := (hTests.2.2 N s hN hCond.1).2
  have hVw : Internal.Subset M.mem V w := fun k hk => ((hV k).mp hk).1
  have hVi : Internal.Infinite M.mem w V := by
    apply (Internal.infinite_iff_unbounded hZF hw' hVw).mpr
    intro i hi
    obtain ⟨b, hb, hNb, hib⟩ := natural_common_bound hZF hw' hN hi
    obtain ⟨F, hF, hFH⟩ := (hTests.2.2 b s hb hCond.1).1
    have hBF : MeetsTests w B F := fun X hXF => hB X (hFH X hXF)
    have hAvoidB : AvoidsTail w A E p B b := by
      intro k hk hkB hbk
      exact hAvoid k hk hkB (atLeast_trans hZF hw hk hNb hbk)
    obtain ⟨k, hk, hbk, hPossible⟩ := hF.2.2 B hBF p hStem hAvoidB
    exact ⟨k, hk, (atLeast_trans hZF hw hk hib hbk).symm,
      (hV k).mpr ⟨hk, atLeast_trans hZF hw hk hNb hbk, hPossible⟩⟩
  obtain ⟨d, hd, hdi⟩ := hB V hVH hVi
  have hdw : Internal.Subset M.mem d w := fun k hk => hVw k ((hd k).mp hk).1
  obtain ⟨zero, _, hz⟩ := hw.1.1
  obtain ⟨k, _, _, hkd⟩ := (Internal.infinite_iff_unbounded hZF hw' hdw).mp hdi zero hz
  obtain ⟨hkV, hkB⟩ := (hd k).mp hkd
  obtain ⟨hk, hNk, hPossible⟩ := (hV k).mp hkV
  obtain ⟨q, hq, hqp, hqk⟩ := hPossible p hStem
  exact hNo ⟨q, k, hq, hqp, hkB, hk, hNk, hqk⟩

theorem tall_tests_exists (hZFC : M.Models SetTheory.ZFC) {w A E : M.Domain}
    (hw : M.IsOmega w) (hUnbounded : UnboundedDecisions w A E)
    (hMono : MonotoneDecisions w A E) : ∃ H, TallTestsWitness w A E H := by
  obtain ⟨H, hH⟩ := total_tail_tests_exists hZFC hw hUnbounded hMono
  exact ⟨H, total_tests_tall (ZFC.models_zf_l hZFC) hw hH⟩

namespace Syntax
def tallDensityFormula {n} (w A E B : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.imp (codedConditionFormula w.weaken.weaken A.weaken.weaken (.bound 1))
    (.imp (.mem .newest w.weaken.weaken)
      (.existsE (.existsE (.conj
        (codedConditionFormula w.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 1))
        (.conj (codedExtendsFormula (.bound 1) (.bound 3))
          (.conj (.mem .newest B.weaken.weaken.weaken.weaken)
            (.conj (.mem .newest w.weaken.weaken.weaken.weaken)
              (.conj (atLeastFormula (.bound 2) .newest)
                (entry_m (.bound 1) .newest E.weaken.weaken.weaken.weaken)))))))))))

def tallTestsWitnessFormula {n} (w A E H : Project.Term n) : Project.Formula 1 n :=
  .conj (.existsE (Internal.Syntax.InjectionFormula .newest H.weaken w.weaken))
    (.conj (.forallE (.imp (.mem .newest H.weaken) (Internal.Syntax.SubsetFormula .newest w.weaken)))
      (.forallE (.imp (meetsTestsFormula w.weaken .newest H.weaken)
        (tallDensityFormula w.weaken A.weaken E.weaken .newest))))

derive_free_closed tallDensityFormula
derive_free_closed tallTestsWitnessFormula

theorem tallDensityFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E B : Project.Term n) : Project.Formula.satisfies ρ (tallDensityFormula w A E B) ↔
      TallDensity (w.eval ρ) (A.eval ρ) (E.eval ρ) (B.eval ρ) := by
  simp only [tallDensityFormula, TallDensity, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, codedConditionFormula_semantics hE,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, codedExtendsFormula_semantics hE,
    atLeastFormula_semantics hE, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem tallTestsWitnessFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E H : Project.Term n) : Project.Formula.satisfies ρ (tallTestsWitnessFormula w A E H) ↔
      TallTestsWitness (w.eval ρ) (A.eval ρ) (E.eval ρ) (H.eval ρ) := by
  simp only [tallTestsWitnessFormula, TallTestsWitness, InternalCountable,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Internal.Syntax.satisfies_InjectionFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Internal.Syntax.satisfies_SubsetFormula hE, meetsTestsFormula_semantics hE,
    tallDensityFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def tallTestsBody : Project.Formula 1 3 :=
  .imp (Project.Formula.isOmega (.bound 2))
    (.imp (unboundedDecisionsFormula (.bound 2) (.bound 1) .newest)
      (.imp (monotoneDecisionsFormula (.bound 2) (.bound 1) .newest)
        (.existsE (tallTestsWitnessFormula (.bound 3) (.bound 2) (.bound 1) .newest))))

theorem tallTestsBody_closed : tallTestsBody.FreeClosed := by
  simp -implicitDefEqProofs [tallTestsBody, Definitional.Formula.FreeClosed]

def tallTestsSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose tallTestsBody) (ObjectTheory.universalClose_closed _ tallTestsBody_closed)

theorem tallTestsBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 3) :
    Project.Formula.satisfies ρ tallTestsBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [tallTestsBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    unboundedDecisionsFormula_semantics hZF.1, monotoneDecisionsFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, tallTestsWitnessFormula_semantics hZF.1]
  exact fun hw hUnbounded hMono => tall_tests_exists hZFC hw hUnbounded hMono
end Syntax

theorem derives_tall_tests : Project.Derives SetTheory.ZFC Syntax.tallTestsSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.tallTestsBody (Syntax.tallTestsBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

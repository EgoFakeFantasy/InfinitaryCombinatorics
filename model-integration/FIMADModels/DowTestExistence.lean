import FIMADModels.DowTestAssembly

/-! Countable tests are constructed from an actual monotone internal decision
relation. The least-closure proof is a first-order set argument in original
ZFC, including internal selection of the tail/test witnesses at each step. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def MonotoneDecisions (w A E : M.Domain) : Prop :=
  ∀ p q k, CodedCondition w A p → CodedCondition w A q →
    CodedExtends (M := M) q p → Entry_d M p k E → Entry_d M q k E

def NaturalDecisions (w A E D : M.Domain) : Prop :=
  ∀ p, M.mem p D → CodedCondition w A p → ∃ k, M.mem k w ∧ Entry_d M p k E

namespace Syntax
def goodStemFormula {n} (w A E s : Project.Term n) : Project.Formula 1 n :=
  .conj (finiteSubsetFormula w s)
    (.existsE (testsWitnessFormula w.weaken A.weaken E.weaken s.weaken .newest))

def selectedTestsFormula {n} (w A E a s i q : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (kpair_m q.weaken.weaken.weaken (.bound 2) (.bound 1))
    (.conj (tailFormula w.weaken.weaken.weaken a.weaken.weaken.weaken i.weaken.weaken.weaken .newest)
      (.conj (Project.Formula.isUnionOfTwo (.bound 2) s.weaken.weaken.weaken .newest)
        (testsWitnessFormula w.weaken.weaken.weaken A.weaken.weaken.weaken
          E.weaken.weaken.weaken (.bound 2) (.bound 1)))))))

def monotoneDecisionsFormula {n} (w A E : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.forallE (.imp (codedConditionFormula w.weaken.weaken.weaken A.weaken.weaken.weaken (.bound 2))
    (.imp (codedConditionFormula w.weaken.weaken.weaken A.weaken.weaken.weaken (.bound 1))
      (.imp (codedExtendsFormula (.bound 1) (.bound 2))
        (.imp (entry_m (.bound 2) .newest E.weaken.weaken.weaken)
          (entry_m (.bound 1) .newest E.weaken.weaken.weaken)))))))

def naturalDecisionsFormula {n} (w A E D : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest D.weaken)
    (.imp (codedConditionFormula w.weaken A.weaken .newest)
      (.existsE (.conj (.mem .newest w.weaken.weaken)
        (entry_m (.bound 1) .newest E.weaken.weaken)))))

derive_free_closed goodStemFormula
derive_free_closed selectedTestsFormula
derive_free_closed monotoneDecisionsFormula
derive_free_closed naturalDecisionsFormula

theorem goodStemFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E s : Project.Term n) : Project.Formula.satisfies ρ (goodStemFormula w A E s) ↔
      FiniteSubset (w.eval ρ) (s.eval ρ) ∧ ∃ F, TestsWitness (w.eval ρ) (A.eval ρ) (E.eval ρ) (s.eval ρ) F := by
  simp only [goodStemFormula, Project.Formula.satisfies_conj_iff, finiteSubsetFormula_semantics hE,
    Project.Formula.satisfies_exists_iff, testsWitnessFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem selectedTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E a s i q : Project.Term n) : Project.Formula.satisfies ρ (selectedTestsFormula w A E a s i q) ↔
      ∃ r F t, KPair_d M (q.eval ρ) r F ∧ Tail (w.eval ρ) (a.eval ρ) (i.eval ρ) t ∧
        M.IsUnionOfTwo r (s.eval ρ) t ∧ TestsWitness (w.eval ρ) (A.eval ρ) (E.eval ρ) r F := by
  simp only [selectedTestsFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, tailFormula_semantics hE,
    Project.Formula.satisfies_isUnionOfTwo_iff, testsWitnessFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem monotoneDecisionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E : Project.Term n) : Project.Formula.satisfies ρ (monotoneDecisionsFormula w A E) ↔
      MonotoneDecisions (w.eval ρ) (A.eval ρ) (E.eval ρ) := by
  simp only [monotoneDecisionsFormula, MonotoneDecisions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, codedConditionFormula_semantics hE,
    codedExtendsFormula_semantics hE, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem naturalDecisionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E D : Project.Term n) : Project.Formula.satisfies ρ (naturalDecisionsFormula w A E D) ↔
      NaturalDecisions (w.eval ρ) (A.eval ρ) (E.eval ρ) (D.eval ρ) := by
  simp only [naturalDecisionsFormula, NaturalDecisions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    codedConditionFormula_semantics hE, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem countable_tests_exists (hZFC : M.Models SetTheory.ZFC) {w A E D : M.Domain}
    (hw : M.IsOmega w) (hDense : DenseConditions w A D)
    (hDec : NaturalDecisions w A E D) (hMono : MonotoneDecisions w A E) :
    ∀ s, FiniteSubset w s → ∃ F, TestsWitness w A E s F := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  let ρ : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E
  let φ : UnarySchema 3 := { body := Syntax.goodStemFormula (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, hP⟩ := ZF.separation_exists_d hZF φ ρ W
  have hp s : M.mem s P ↔ FiniteSubset w s ∧ ∃ F, TestsWitness w A E s F := by
    rw [hP s]
    have hφ : φ.denote ρ s ↔ FiniteSubset w s ∧ ∃ F, TestsWitness w A E s F :=
      Syntax.goodStemFormula_semantics hZF.1 _ _ _ _ _
    change M.mem s W ∧ φ.denote ρ s ↔ _
    rw [hφ]
    exact ⟨And.right, fun h => ⟨(hW s).mpr h.1.1, h⟩⟩
  have hClosed : ReachClosed w A D P := by
    refine ⟨fun s hs => ((hp s).mp hs).1, ?_, ?_⟩
    · intro s p hpD hStem
      obtain ⟨S, hps, hCond⟩ := hStem
      obtain ⟨k, hkw, hpk⟩ := hDec p hpD ⟨s, S, hps, hCond⟩
      have hPossible : PossibleValue w A E s k := by
        intro q hq
        obtain ⟨T, hqt, hT⟩ := hq
        obtain ⟨U, _, hU, hUS, hUT⟩ := same_stem_merge hZF
          ((Internal.omega_native_iff hZF.1 w).mpr hw) hCond hT
        obtain ⟨r, hr⟩ := I.total s U
        have hrCond : CodedCondition w A r := ⟨s, U, hr, hU⟩
        have hrp : CodedExtends (M := M) r p := ⟨s, U, s, S, hr, hps, hUS⟩
        exact ⟨r, hrCond, ⟨s, U, s, T, hr, hqt, hUT⟩,
          hMono p r k ⟨s, S, hps, hCond⟩ hrCond hrp hpk⟩
      exact (hp s).mpr ⟨hCond.1, empty_tests hZF hkw hPossible⟩
    · intro s a hs ha hReady
      obtain ⟨K, hK⟩ := ZF.exists_powerSet hZF W
      obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I W K
      let η : Env M 5 := (ρ.push a).push s
      let ψ : BinarySchema 5 := {
        body := Syntax.selectedTestsFormula (.bound 6) (.bound 5) (.bound 4)
          (.bound 3) (.bound 2) (.bound 1) .newest }
      have hψ n q : ψ.denote η n q ↔ ∃ r F t, KPair_d M q r F ∧
          Tail w a n t ∧ M.IsUnionOfTwo r s t ∧ TestsWitness w A E r F :=
        Syntax.selectedTestsFormula_semantics hZF.1 _ _ _ _ _ _ _ _
      obtain ⟨G, hG, he⟩ := ZFC.uniformize_formula_l I hZFC ψ η (X := w) (Y := Q) (by
        intro n hn
        obtain ⟨t, r, ht, hr, hrP⟩ := hReady n hn
        obtain ⟨hrf, F, hF⟩ := (hp r).mp hrP
        obtain ⟨q, hq⟩ := I.total r F
        have hFW : M.MemberSubset F W := fun X hX => (hW X).mpr (hF.2.1 X hX)
        exact ⟨q, (hQ q).mpr ⟨r, (hW r).mpr hrf.1, F, (hK F).mpr hFW, hq⟩,
          (hψ n q).mpr ⟨r, F, t, hq, ht, hr, hF⟩⟩)
      have hSelected : SelectedTests w A E a s G := by
        intro n hn
        obtain ⟨q, _, hnq⟩ := hG.2.2 n hn
        obtain ⟨r, F, t, hqrF, ht, hr, hF⟩ := (hψ n q).mp (he n q hnq)
        exact ⟨q, r, F, t, hnq, hqrF, ht, hr, hF⟩
      exact (hp s).mpr ⟨hs, assemble_selected_tests hZFC hw ha hs hSelected hG.1.2⟩
  exact fun s hs => ((hp s).mp (dense_reach_all hZF hDense hClosed s hs)).2

namespace Syntax
def testsExistBody : Project.Formula 1 4 :=
  .imp (Project.Formula.isOmega (.bound 3))
    (.imp (denseConditionsFormula (.bound 3) (.bound 2) .newest)
      (.imp (naturalDecisionsFormula (.bound 3) (.bound 2) (.bound 1) .newest)
        (.imp (monotoneDecisionsFormula (.bound 3) (.bound 2) (.bound 1))
          (.forallE (.imp (finiteSubsetFormula (.bound 4) .newest)
            (.existsE (testsWitnessFormula (.bound 5) (.bound 4) (.bound 3) (.bound 1) .newest)))))))

theorem testsExistBody_closed : testsExistBody.FreeClosed := by
  simp -implicitDefEqProofs [testsExistBody, Definitional.Formula.FreeClosed]

def testsExistSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose testsExistBody)
  (ObjectTheory.universalClose_closed _ testsExistBody_closed)

theorem testsExistBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 4) :
    Project.Formula.satisfies ρ testsExistBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [testsExistBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    denseConditionsFormula_semantics hZF.1, naturalDecisionsFormula_semantics hZF.1,
    monotoneDecisionsFormula_semantics hZF.1, Project.Formula.satisfies_forall_iff,
    finiteSubsetFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
    testsWitnessFormula_semantics hZF.1]
  exact fun hw hDense hDec hMono => countable_tests_exists hZFC hw hDense hDec hMono
end Syntax

theorem derives_countable_tests : Project.Derives SetTheory.ZFC Syntax.testsExistSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.testsExistBody (Syntax.testsExistBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

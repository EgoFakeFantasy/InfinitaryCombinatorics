import FIMADModels.DowReach
import YesMetaZFC.SetTheory.CollectionChoice

/-! Common possible values of an actual internal decision relation. Finite
elimination chooses an internal graph and merges its internally finite range.
No model-external choice function is used as an internal set. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def PossibleValue (w A E s k : M.Domain) : Prop :=
  ∀ p, SameStem w A s p → ∃ q,
    CodedCondition w A q ∧ CodedExtends (M := M) q p ∧ Entry_d M q k E

def AvoidValue (w A E p k : M.Domain) : Prop :=
  ∀ q, CodedCondition w A q → CodedExtends (M := M) q p → ¬ Entry_d M q k E

namespace Syntax
def possibleValueFormula {n} (w A E s k : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (sameStemFormula w.weaken A.weaken s.weaken .newest)
    (.existsE (.conj (codedConditionFormula w.weaken.weaken A.weaken.weaken .newest)
      (.conj (codedExtendsFormula .newest (.bound 1))
        (entry_m .newest k.weaken.weaken E.weaken.weaken)))))

def avoidValueFormula {n} (w A E p k : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (codedConditionFormula w.weaken A.weaken .newest)
    (.imp (codedExtendsFormula .newest p.weaken)
      (.neg (entry_m .newest k.weaken E.weaken))))

derive_free_closed possibleValueFormula
derive_free_closed avoidValueFormula

theorem possibleValueFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E s k : Project.Term n) : Project.Formula.satisfies ρ (possibleValueFormula w A E s k) ↔
      PossibleValue (w.eval ρ) (A.eval ρ) (E.eval ρ) (s.eval ρ) (k.eval ρ) := by
  simp only [possibleValueFormula, PossibleValue, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, sameStemFormula_semantics hE,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    codedConditionFormula_semantics hE, codedExtendsFormula_semantics hE, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem avoidValueFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E p k : Project.Term n) : Project.Formula.satisfies ρ (avoidValueFormula w A E p k) ↔
      AvoidValue (w.eval ρ) (A.eval ρ) (E.eval ρ) (p.eval ρ) (k.eval ρ) := by
  simp only [avoidValueFormula, AvoidValue, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, codedConditionFormula_semantics hE,
    codedExtendsFormula_semantics hE, Project.Formula.satisfies_neg_iff, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax

theorem possible_values_exists (hZF : M.Models SetTheory.ZF) (w A E s : M.Domain) :
    ∃ V, ∀ k, M.mem k V ↔ M.mem k w ∧ PossibleValue w A E s k := by
  let ρ : Env M 4 := (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E).push s
  let φ : UnarySchema 4 := {
    body := Syntax.possibleValueFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨V, hV⟩ := ZF.separation_exists_d hZF φ ρ w
  exact ⟨V, fun k => (hV k).trans (and_congr_right fun _ =>
    Syntax.possibleValueFormula_semantics hZF.1 _ _ _ _ _ _)⟩

theorem avoider_of_not_possible {w A E s k : M.Domain}
    (hk : ¬ PossibleValue w A E s k) :
    ∃ p, SameStem w A s p ∧ AvoidValue w A E p k := by
  classical
  apply Classical.byContradiction
  intro hNoBad
  apply hk
  intro p hp
  apply Classical.byContradiction
  intro hNoGood
  exact hNoBad ⟨p, hp, fun q hq hqp hEntry => hNoGood ⟨q, hq, hqp, hEntry⟩⟩

/-- A finite set of impossible values can be simultaneously excluded. -/
theorem finite_impossible_elimination (hZFC : M.Models SetTheory.ZFC) {w A E s V : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) (hV : Internal.Finite M.mem w V)
    (hImpossible : ∀ k, M.mem k V → ¬ PossibleValue w A E s k) :
    ∃ q, SameStem w A s q ∧ ∀ k, M.mem k V → AvoidValue w A E q k := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 4 := (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push E).push s
  let φ : BinarySchema 4 := {
    body := .conj (Syntax.sameStemFormula (.bound 5) (.bound 4) (.bound 2) .newest)
      (Syntax.avoidValueFormula (.bound 5) (.bound 4) (.bound 3) .newest (.bound 1)) }
  have hφ k p : φ.denote ρ k p ↔ SameStem w A s p ∧ AvoidValue w A E p k := by
    simp only [BinarySchema.denote, φ, Project.Formula.satisfies_conj_iff,
      Syntax.sameStemFormula_semantics hZF.1, Syntax.avoidValueFormula_semantics hZF.1]
    rfl
  obtain ⟨Y, F, hF, hGraph⟩ := ZFC.collect_choice_l I hZFC φ ρ V (fun k hk => by
    obtain ⟨p, hp⟩ := avoider_of_not_possible (hImpossible k hk)
    exact ⟨p, (hφ k p).mpr hp⟩)
  obtain ⟨P, hP⟩ := ZF.exists_range_of_setFunction hZF I hF.1 hF.2.1
  have hFP : M.IsSetFunctionFromTo I F V P := ⟨hF.1, hF.2.1, fun k hk => by
    obtain ⟨p, _, hkp⟩ := hF.2.2 k hk
    exact ⟨p, (hP p).mpr ⟨k, hkp⟩, hkp⟩⟩
  have hSurj : M.IsSetSurjectiveOnto I F V P := fun p hp => by
    obtain ⟨k, hkp⟩ := (hP p).mp hp
    exact ⟨k, hF.input_mem_of_pairMember hkp, hkp⟩
  obtain ⟨n, hn, j, hj⟩ := (ForcingFinite.finite_correct hZF w V).mp hV
  obtain ⟨f, hf⟩ := ZFC.surjection_bound_l I hZFC hFP hSurj
  have hPf : Internal.Finite M.mem w P := (ForcingFinite.finite_correct hZF w P).mpr
    ⟨n, hn, ZF.exists_compositionInjection hZF I hf hj⟩
  have hFamily : SameStemFamily w A s P := fun p hp => by
    obtain ⟨k, hkp⟩ := (hP p).mp hp
    exact ((hφ k p).mp (hGraph k p hkp)).1
  obtain ⟨q, hq, hqP⟩ := finite_same_stem_amalgam hZF hw hs hPf hFamily
  refine ⟨q, hq, fun k hk r hr hrq => ?_⟩
  obtain ⟨p, _, hkp⟩ := hF.2.2 k hk
  have hBad := ((hφ k p).mp (hGraph k p hkp)).2
  exact hBad r hr (coded_extends_trans hZF hrq (hqP p ((hP p).mpr ⟨k, hkp⟩)))

namespace Syntax
open Internal.Syntax
def eliminationBody : Project.Formula 1 5 :=
  .imp (Project.Formula.isOmega (.bound 4))
    (.imp (finiteSubsetFormula (.bound 4) (.bound 1))
      (.imp (FiniteFormula (.bound 4) .newest)
        (.imp (.forallE (.imp (.mem .newest (.bound 1))
          (.neg (possibleValueFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) .newest))))
          (.existsE (.conj (sameStemFormula (.bound 5) (.bound 4) (.bound 2) .newest)
            (.forallE (.imp (.mem .newest (.bound 2))
              (avoidValueFormula (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest))))))))

theorem eliminationBody_closed : eliminationBody.FreeClosed := by
  simp -implicitDefEqProofs [eliminationBody, Definitional.Formula.FreeClosed]

def eliminationSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose eliminationBody)
  (ObjectTheory.universalClose_closed _ eliminationBody_closed)

theorem eliminationBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 5) :
    Project.Formula.satisfies ρ eliminationBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [eliminationBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, finiteSubsetFormula_semantics hZF.1,
    satisfies_FiniteFormula hZF.1, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_neg_iff,
    possibleValueFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, sameStemFormula_semantics hZF.1,
    avoidValueFormula_semantics hZF.1]
  exact fun hw hs hV hImpossible => finite_impossible_elimination hZFC hw hs hV hImpossible
end Syntax

theorem derives_finite_elimination : Project.Derives SetTheory.ZFC Syntax.eliminationSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.eliminationBody (Syntax.eliminationBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

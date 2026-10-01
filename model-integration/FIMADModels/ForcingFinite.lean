import FIMADModels.ObjectTheory
import YesMetaZFC.Model.Forcing.Internal.Names.Pair
import YesMetaZFC.SetTheory.Card.Finite

/-! Exact bridge between the manuscript and the internal forcing library.
Both use Kuratowski pairs and injections into an element of the given omega
set. The equivalence is proved in the original ZF derivation kernel. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.ForcingFinite
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem pair_correct (p a b : M.Domain) :
    KPair_d M p a b ↔ Internal.Pair M.mem p a b := Iff.rfl

theorem injection_correct (hZF : M.Models SetTheory.ZF) (f a b : M.Domain) :
    Internal.Injection M.mem f a b ↔ M.IsSetInjectionFromTo
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) f a b :=
  Internal.injection_native_iff hZF f a b

theorem finite_correct (hZF : M.Models SetTheory.ZF) (w a : M.Domain) :
    Internal.Finite M.mem w a ↔ Finite_d
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) w a := by
  constructor
  · rintro ⟨n, hn, f, hf⟩
    exact ⟨n, hn, f, (injection_correct hZF f a n).mp hf⟩
  · rintro ⟨n, hn, f, hf⟩
    exact ⟨n, hn, f, (injection_correct hZF f a n).mpr hf⟩

def bridgeBody : Project.Formula 1 2 :=
  .iff (Internal.Syntax.FiniteFormula (.bound 1) (.bound 0))
    (finite_m kpair_convention_l (.bound 1) (.bound 0))

theorem bridgeBody_closed : bridgeBody.FreeClosed := by
  simp only [bridgeBody, Definitional.Formula.FreeClosed]
  exact ⟨Internal.Syntax.closed_FiniteFormula _ _ rfl rfl,
    finite_m_freeClosed _ _ _ rfl rfl⟩

def bridgeSentence : Project.Sentence := Project.Sentence.ofFormula
  (.forallE (.forallE bridgeBody))
  (by simpa only [Definitional.Formula.FreeClosed] using bridgeBody_closed)

/-- Original finite-set formula and the forcing library's formula are
provably equivalent for every set, including in nonstandard ZF models. -/
theorem derives_finite_bridge : Project.Derives SetTheory.ZF bridgeSentence := by
  apply YesMetaZFC.Logic.FirstOrder.Completeness.strong_completeness ObjectTheory.membershipSchedule
  intro M hM
  have hZF := ObjectTheory.native_zf_of_typed hM
  apply (FirstOrderSemantics.sentence_correct hZF.1 bridgeSentence).mpr
  let N := FirstOrderSemantics.reduct M
  let I := kpair_interpretation_l N hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  rw [SetTheory.Structure.satisfiesSentence_iff]
  simp only [bridgeSentence, Project.Sentence.ofFormula, bridgeBody,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Internal.Syntax.satisfies_FiniteFormula hZF.1, finite_sat_l I hZF.1]
  intro free w a
  exact finite_correct hZF w a

end InfinitaryCombinatorics.Formalizations.FIMAD.ForcingFinite

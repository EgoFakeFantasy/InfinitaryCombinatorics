import FIMADModels.DowPossible

/-! The finite-tail step in Dow's common-possible-values argument, entirely
inside the arbitrary ZFC model. Tail witnesses need not be assembled into an
external sequence, and the finite value set may be nonstandard finite. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def FiniteTailWitnesses (w A E a s N V : M.Domain) : Prop :=
  ∀ n, M.mem n w → AtLeast (M := M) N n → ∃ t r k,
    Tail w a n t ∧ M.IsUnionOfTwo r s t ∧ PossibleValue w A E r k ∧ M.mem k V

theorem possible_of_finite_tail (hZFC : M.Models SetTheory.ZFC) {w A E a s N V : M.Domain}
    (hw : M.IsOmega w) (ha : M.mem a A) (hs : FiniteSubset w s) (hN : M.mem N w)
    (hV : Internal.Finite M.mem w V) (hTail : FiniteTailWitnesses w A E a s N V) :
    ∃ k, M.mem k V ∧ PossibleValue w A E s k := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  classical
  apply Classical.byContradiction
  intro hNoPossible
  have hImpossible : ∀ k, M.mem k V → ¬ PossibleValue w A E s k :=
    fun k hk hPossible => hNoPossible ⟨k, hk, hPossible⟩
  obtain ⟨q, ⟨S, hq, hCond⟩, hAvoid⟩ := finite_impossible_elimination hZFC hw hs hV hImpossible
  obtain ⟨m, hm, hAllow⟩ := hCond.2.2.2 s hs hCond.2.2.1 a ha
  obtain ⟨n, hn, hNn, hmn⟩ := natural_common_bound hZF
    ((Internal.omega_native_iff hZF.1 w).mpr hw) hN hm
  obtain ⟨t, r, k, ht, hr, hk, hkV⟩ := hTail n hn hNn
  have ht' : Tail w a m t := tail_mono hZF
    ((Internal.omega_native_iff hZF.1 w).mpr hw) hmn ht
  have hrS := hAllow t ht' r hr
  have hRestem : Condition w A r S :=
    ⟨finiteSubset_union hZF hw hs ht.1 hr, hCond.2.1, hrS, hCond.2.2.2⟩
  obtain ⟨p, hp⟩ := I.total r S
  have hpq : CodedExtends (M := M) p q :=
    ⟨r, S, s, S, hp, hq, (fun x hx => (hr x).mpr (Or.inl hx)),
      (fun _ h => h), hrS⟩
  obtain ⟨v, hv, hvp, hvk⟩ := hk p ⟨S, hp, hRestem⟩
  exact hAvoid k hkV v hv (coded_extends_trans hZF hvp hpq) hvk

namespace Syntax
open Internal.Syntax
def finiteTailFormula {n} (w A E a s N V : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest w.weaken)
    (.imp (atLeastFormula N.weaken .newest)
      (.existsE (.existsE (.existsE (.conj
        (tailFormula w.weaken.weaken.weaken.weaken a.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
        (.conj (Project.Formula.isUnionOfTwo (.bound 1) s.weaken.weaken.weaken.weaken (.bound 2))
          (.conj (possibleValueFormula w.weaken.weaken.weaken.weaken
            A.weaken.weaken.weaken.weaken E.weaken.weaken.weaken.weaken (.bound 1) .newest)
            (.mem .newest V.weaken.weaken.weaken.weaken)))))))))

derive_free_closed finiteTailFormula

theorem finiteTailFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E a s N V : Project.Term n) : Project.Formula.satisfies ρ (finiteTailFormula w A E a s N V) ↔
      FiniteTailWitnesses (w.eval ρ) (A.eval ρ) (E.eval ρ) (a.eval ρ) (s.eval ρ) (N.eval ρ) (V.eval ρ) := by
  simp only [finiteTailFormula, FiniteTailWitnesses, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    atLeastFormula, AtLeast, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, tailFormula_semantics hE,
    Project.Formula.satisfies_isUnionOfTwo_iff, possibleValueFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def finiteTailBody : Project.Formula 1 7 :=
  .imp (Project.Formula.isOmega (.bound 6))
    (.imp (.mem (.bound 3) (.bound 5))
      (.imp (finiteSubsetFormula (.bound 6) (.bound 2))
        (.imp (.mem (.bound 1) (.bound 6))
          (.imp (FiniteFormula (.bound 6) .newest)
            (.imp (finiteTailFormula (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)
              (.existsE (.conj (.mem .newest (.bound 1))
                (possibleValueFormula (.bound 7) (.bound 6) (.bound 5) (.bound 3) .newest))))))))

theorem finiteTailBody_closed : finiteTailBody.FreeClosed := by
  simp -implicitDefEqProofs [finiteTailBody, Definitional.Formula.FreeClosed]

def finiteTailSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose finiteTailBody)
  (ObjectTheory.universalClose_closed _ finiteTailBody_closed)

theorem finiteTailBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 7) :
    Project.Formula.satisfies ρ finiteTailBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [finiteTailBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_mem_iff,
    finiteSubsetFormula_semantics hZF.1, satisfies_FiniteFormula hZF.1,
    finiteTailFormula_semantics hZF.1, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, possibleValueFormula_semantics hZF.1]
  exact fun hw ha hs hN hV hTail => possible_of_finite_tail hZFC hw ha hs hN hV hTail
end Syntax

theorem derives_finite_tail : Project.Derives SetTheory.ZFC Syntax.finiteTailSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.finiteTailBody (Syntax.finiteTailBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

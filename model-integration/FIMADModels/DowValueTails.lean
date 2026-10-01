import FIMADModels.DowTestExistence

/-! Restricted decision relations and tests at every internal natural bound.
Both the restricted relation and its dense deciding set are constructed inside
the ground model. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def TailRelation (w A E N F : M.Domain) : Prop :=
  ∀ p k, Entry_d M p k F ↔ CodedCondition w A p ∧ M.mem k w ∧
    AtLeast (M := M) N k ∧ Entry_d M p k E

def UnboundedDecisions (w A E : M.Domain) : Prop :=
  ∀ p N, CodedCondition w A p → M.mem N w → ∃ q k,
    CodedCondition w A q ∧ CodedExtends (M := M) q p ∧
      M.mem k w ∧ AtLeast (M := M) N k ∧ Entry_d M q k E

def AvoidsTail (w A E p B N : M.Domain) : Prop :=
  ∀ k, M.mem k w → M.mem k B → AtLeast (M := M) N k → AvoidValue w A E p k

def TailTests (w A E N s H : M.Domain) : Prop :=
  InternalCountable w H ∧ (∀ X, M.mem X H → Internal.Subset M.mem X w) ∧
  ∀ B, MeetsTests w B H → ∀ p, SameStem w A s p → AvoidsTail w A E p B N →
    ∃ k, M.mem k w ∧ AtLeast (M := M) N k ∧ PossibleValue w A E s k

namespace Syntax
def tailRelationFormula {n} (w A E N F : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.iff (entry_m (.bound 1) .newest F.weaken.weaken)
    (.conj (codedConditionFormula w.weaken.weaken A.weaken.weaken (.bound 1))
      (.conj (.mem .newest w.weaken.weaken)
        (.conj (atLeastFormula N.weaken.weaken .newest) (entry_m (.bound 1) .newest E.weaken.weaken))))))

def unboundedDecisionsFormula {n} (w A E : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.imp (codedConditionFormula w.weaken.weaken A.weaken.weaken (.bound 1))
    (.imp (.mem .newest w.weaken.weaken)
      (.existsE (.existsE (.conj (codedConditionFormula w.weaken.weaken.weaken.weaken A.weaken.weaken.weaken.weaken (.bound 1))
        (.conj (codedExtendsFormula (.bound 1) (.bound 3))
          (.conj (.mem .newest w.weaken.weaken.weaken.weaken)
            (.conj (atLeastFormula (.bound 2) .newest)
              (entry_m (.bound 1) .newest E.weaken.weaken.weaken.weaken))))))))))

def avoidsTailFormula {n} (w A E p B N : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest w.weaken) (.imp (.mem .newest B.weaken)
    (.imp (atLeastFormula N.weaken .newest)
      (avoidValueFormula w.weaken A.weaken E.weaken p.weaken .newest))))

def tailTestsFormula {n} (w A E N s H : Project.Term n) : Project.Formula 1 n :=
  .conj (.existsE (Internal.Syntax.InjectionFormula .newest H.weaken w.weaken))
    (.conj (.forallE (.imp (.mem .newest H.weaken) (Internal.Syntax.SubsetFormula .newest w.weaken)))
      (.forallE (.imp (meetsTestsFormula w.weaken .newest H.weaken)
        (.forallE (.imp (sameStemFormula w.weaken.weaken A.weaken.weaken s.weaken.weaken .newest)
          (.imp (avoidsTailFormula w.weaken.weaken A.weaken.weaken E.weaken.weaken .newest (.bound 1) N.weaken.weaken)
            (.existsE (.conj (.mem .newest w.weaken.weaken.weaken)
              (.conj (atLeastFormula N.weaken.weaken.weaken .newest)
                (possibleValueFormula w.weaken.weaken.weaken A.weaken.weaken.weaken
                  E.weaken.weaken.weaken s.weaken.weaken.weaken .newest))))))))))

derive_free_closed tailRelationFormula
derive_free_closed unboundedDecisionsFormula
derive_free_closed avoidsTailFormula
derive_free_closed tailTestsFormula

theorem atLeastFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (N k : Project.Term n) : Project.Formula.satisfies ρ (atLeastFormula N k) ↔
      AtLeast (M := M) (N.eval ρ) (k.eval ρ) := by
  simp only [atLeastFormula, AtLeast, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE, Project.Formula.satisfies_mem_iff]

theorem tailRelationFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E N F : Project.Term n) : Project.Formula.satisfies ρ (tailRelationFormula w A E N F) ↔
      TailRelation (w.eval ρ) (A.eval ρ) (E.eval ρ) (N.eval ρ) (F.eval ρ) := by
  simp only [tailRelationFormula, TailRelation, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, entry_sat_l M hE,
    Project.Formula.satisfies_conj_iff, codedConditionFormula_semantics hE,
    Project.Formula.satisfies_mem_iff, atLeastFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem unboundedDecisionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E : Project.Term n) : Project.Formula.satisfies ρ (unboundedDecisionsFormula w A E) ↔
      UnboundedDecisions (w.eval ρ) (A.eval ρ) (E.eval ρ) := by
  simp only [unboundedDecisionsFormula, UnboundedDecisions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, codedConditionFormula_semantics hE,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, codedExtendsFormula_semantics hE,
    atLeastFormula_semantics hE, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem avoidsTailFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E p B N : Project.Term n) : Project.Formula.satisfies ρ (avoidsTailFormula w A E p B N) ↔
      AvoidsTail (w.eval ρ) (A.eval ρ) (E.eval ρ) (p.eval ρ) (B.eval ρ) (N.eval ρ) := by
  simp only [avoidsTailFormula, AvoidsTail, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    atLeastFormula_semantics hE, avoidValueFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem tailTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A E N s H : Project.Term n) : Project.Formula.satisfies ρ (tailTestsFormula w A E N s H) ↔
      TailTests (w.eval ρ) (A.eval ρ) (E.eval ρ) (N.eval ρ) (s.eval ρ) (H.eval ρ) := by
  simp only [tailTestsFormula, TailTests, InternalCountable, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff, Internal.Syntax.satisfies_InjectionFormula hE,
    Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff, Internal.Syntax.satisfies_SubsetFormula hE,
    meetsTestsFormula_semantics hE, sameStemFormula_semantics hE,
    avoidsTailFormula_semantics hE, atLeastFormula_semantics hE,
    possibleValueFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem tail_relation_exists (hZF : M.Models SetTheory.ZF) (w A E N : M.Domain) :
    ∃ F, TailRelation w A E N F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, hB⟩ := carrier_exists hZF w A
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B w
  let ρ : Env M 2 := (⟨fun _ => E, fun _ => E⟩ : Env M 1).push N
  let φ : BinarySchema 2 := {
    body := .conj (Syntax.atLeastFormula (.bound 2) .newest) (entry_m (.bound 1) .newest (.bound 3)) }
  have hφ p k : φ.denote ρ p k ↔ AtLeast (M := M) N k ∧ Entry_d M p k E := by
    simp only [BinarySchema.denote, φ, Project.Formula.satisfies_conj_iff,
      Syntax.atLeastFormula_semantics hZF.1, entry_sat_l M hZF.1]
    rfl
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  have hf x : M.mem x F ↔ ∃ p k, M.mem p B ∧ M.mem k w ∧ KPair_d M x p k ∧
      AtLeast (M := M) N k ∧ Entry_d M p k E := by
    rw [hF x, hP x, Project.Formula.satisfies_relationMember_iff I φ ρ x]
    constructor
    · rintro ⟨⟨p, hp, k, hk, hcode⟩, p', k', hcode', hφ'⟩
      obtain ⟨rfl, rfl⟩ := I.injective hcode hcode'
      exact ⟨p, k, hp, hk, hcode, (hφ p k).mp hφ'⟩
    · rintro ⟨p, k, hp, hk, hcode, hNk, hpk⟩
      exact ⟨⟨p, hp, k, hk, hcode⟩, p, k, hcode, (hφ p k).mpr ⟨hNk, hpk⟩⟩
  refine ⟨F, fun p k => ?_⟩
  constructor
  · rintro ⟨x, hx, hxF⟩
    obtain ⟨p', k', hp', hk', hx', hNk, hpk⟩ := (hf x).mp hxF
    obtain ⟨rfl, rfl⟩ := I.injective hx hx'
    exact ⟨(hB p).mp hp', hk', hNk, hpk⟩
  · rintro ⟨hp, hk, hNk, hpk⟩
    obtain ⟨x, hx⟩ := I.total p k
    exact ⟨x, hx, (hf x).mpr ⟨p, k, (hB p).mpr hp, hk, hx, hNk, hpk⟩⟩

theorem same_stem_exists (hZF : M.Models SetTheory.ZF) {w A s : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) : ∃ p, SameStem w A s p := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨S, hS⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨p, hp⟩ := I.total s S
  exact ⟨p, S, hp, hs, (fun t ht => False.elim (hS t ht)), hS s,
    fun t _ _ a _ => hw.1.1.elim fun n hn => ⟨n, hn.2, fun v _ r _ => hS r⟩⟩

theorem possible_tail_iff (hZF : M.Models SetTheory.ZF) {w A E N F s k : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) (hF : TailRelation w A E N F) :
    PossibleValue w A F s k ↔ M.mem k w ∧ AtLeast (M := M) N k ∧ PossibleValue w A E s k := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := same_stem_exists hZF hw hs
    obtain ⟨q, _, _, hqk⟩ := h p hp
    obtain ⟨_, hk, hNk, _⟩ := (hF q k).mp hqk
    exact ⟨hk, hNk, fun p hp => (h p hp).elim fun q hq =>
      ⟨q, hq.1, hq.2.1, ((hF q k).mp hq.2.2).2.2.2⟩⟩
  · rintro ⟨hk, hNk, h⟩
    intro p hp
    obtain ⟨q, hq, hqp, hqk⟩ := h p hp
    exact ⟨q, hq, hqp, (hF q k).mpr ⟨hq, hk, hNk, hqk⟩⟩

theorem tail_tests_exists (hZFC : M.Models SetTheory.ZFC) {w A E N s : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) (hN : M.mem N w)
    (hUnbounded : UnboundedDecisions w A E) (hMono : MonotoneDecisions w A E) :
    ∃ H, TailTests w A E N s H := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨F, hF⟩ := tail_relation_exists hZF w A E N
  obtain ⟨B, hB⟩ := carrier_exists hZF w A
  let ρ : Env M 2 := (⟨fun _ => w, fun _ => w⟩ : Env M 1).push F
  let φ : UnarySchema 2 := {
    body := .existsE (.conj (.mem .newest (.bound 3)) (entry_m (.bound 1) .newest (.bound 2))) }
  have hφ p : φ.denote ρ p ↔ ∃ k, M.mem k w ∧ Entry_d M p k F := by
    simp only [UnarySchema.denote, φ, Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff, entry_sat_l M hZF.1]
    rfl
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  have hd p : M.mem p D ↔ CodedCondition w A p ∧ ∃ k, M.mem k w ∧ Entry_d M p k F := by
    rw [hD p]
    change M.mem p B ∧ φ.denote ρ p ↔ _
    rw [hB p, hφ p]
  have hDense : DenseConditions w A D := by
    intro p hp
    obtain ⟨q, k, hq, hqp, hk, hNk, hqk⟩ := hUnbounded p N hp hN
    exact ⟨q, (hd q).mpr ⟨hq, k, hk, (hF q k).mpr ⟨hq, hk, hNk, hqk⟩⟩, hq, hqp⟩
  have hDec : NaturalDecisions w A F D := fun p hp _ => ((hd p).mp hp).2
  have hMonoF : MonotoneDecisions w A F := by
    intro p q k hp hq hqp hpk
    obtain ⟨_, hk, hNk, hpk⟩ := (hF p k).mp hpk
    exact (hF q k).mpr ⟨hq, hk, hNk, hMono p q k hp hq hqp hpk⟩
  obtain ⟨H, hH⟩ := countable_tests_exists hZFC hw hDense hDec hMonoF s hs
  refine ⟨H, hH.1, hH.2.1, fun C hC p hp hAvoid => ?_⟩
  have hAvoidF : AvoidsValues w A F p C := by
    intro k hk q hq hqp hqk
    obtain ⟨_, hkw, hNk, hqk⟩ := (hF q k).mp hqk
    exact hAvoid k hkw hk hNk q hq hqp hqk
  obtain ⟨k, _, hk⟩ := hH.2.2 C hC p hp hAvoidF
  exact ⟨k, (possible_tail_iff hZF hw hs hF).mp hk⟩

namespace Syntax
def tailTestsBody : Project.Formula 1 5 :=
  .imp (Project.Formula.isOmega (.bound 4))
    (.imp (finiteSubsetFormula (.bound 4) .newest)
      (.imp (.mem (.bound 1) (.bound 4))
        (.imp (unboundedDecisionsFormula (.bound 4) (.bound 3) (.bound 2))
          (.imp (monotoneDecisionsFormula (.bound 4) (.bound 3) (.bound 2))
            (.existsE (tailTestsFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))
theorem tailTestsBody_closed : tailTestsBody.FreeClosed := by
  simp -implicitDefEqProofs [tailTestsBody, Definitional.Formula.FreeClosed]
def tailTestsSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose tailTestsBody) (ObjectTheory.universalClose_closed _ tailTestsBody_closed)
theorem tailTestsBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 5) :
    Project.Formula.satisfies ρ tailTestsBody := by
  let hZF := ZFC.models_zf_l hZFC
  simp only [tailTestsBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    finiteSubsetFormula_semantics hZF.1, Project.Formula.satisfies_mem_iff,
    unboundedDecisionsFormula_semantics hZF.1, monotoneDecisionsFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, tailTestsFormula_semantics hZF.1]
  exact fun hw hs hN hUnbounded hMono => tail_tests_exists hZFC hw hs hN hUnbounded hMono
end Syntax

theorem derives_tail_tests : Project.Derives SetTheory.ZFC Syntax.tailTestsSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.tailTestsBody (Syntax.tailTestsBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

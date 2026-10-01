import FIMADModels.DowAvoid

/-! Actual internal union of stems and the original finite/infinite separator.
The object theorem has explicit directed-set and meeting hypotheses. It does
not assume or claim the existence of a ground-model generic filter. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def StemMember (G k : M.Domain) : Prop :=
  ∃ p s S, M.mem p G ∧ KPair_d M p s S ∧ M.mem k s

def Conditions (w A G : M.Domain) : Prop :=
  ∀ p, M.mem p G → CodedCondition w A p

def Directed (G : M.Domain) : Prop :=
  ∀ p q, M.mem p G → M.mem q G →
    ∃ r, M.mem r G ∧ CodedExtends (M := M) r p ∧ CodedExtends (M := M) r q

def MeetsHit (w A G : M.Domain) : Prop :=
  ∀ a n, M.mem a A → M.mem n w → ∃ p, M.mem p G ∧ Hit a n p

def MeetsAvoid (w C G : M.Domain) : Prop :=
  ∀ b, M.mem b C → ∃ p, M.mem p G ∧ Avoid w b p

def WeakSeparator (w A C X : M.Domain) : Prop :=
  Internal.Subset M.mem X w ∧
    (∀ a, M.mem a A → Internal.InfiniteInter M.mem w a X) ∧
    ∀ b, M.mem b C → ∃ d, Internal.Inter M.mem d b X ∧ Internal.Finite M.mem w d

namespace Syntax
open Internal.Syntax

def stemMemberFormula {n} (G k : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (.mem (.bound 2) G.weaken.weaken.weaken)
    (.conj (kpair_m (.bound 2) (.bound 1) .newest) (.mem k.weaken.weaken.weaken (.bound 1))))))

def hitFormula {n} (a k p : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m p.weaken.weaken (.bound 1) .newest)
    (stemHitFormula a.weaken.weaken k.weaken.weaken (.bound 1))))

def avoidFormula {n} (w b p : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m p.weaken.weaken (.bound 1) .newest)
    (stemAvoidFormula w.weaken.weaken b.weaken.weaken (.bound 1) .newest)))

derive_free_closed stemMemberFormula
derive_free_closed hitFormula
derive_free_closed avoidFormula

theorem stemMemberFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (G k : Project.Term n) : Project.Formula.satisfies ρ (stemMemberFormula G k) ↔
      StemMember (G.eval ρ) (k.eval ρ) := by
  simp only [stemMemberFormula, StemMember, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff, kpair_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem hitFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (a k p : Project.Term n) : Project.Formula.satisfies ρ (hitFormula a k p) ↔
      Hit (a.eval ρ) (k.eval ρ) (p.eval ρ) := by
  simp only [hitFormula, Hit, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, stemHitFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem avoidFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w b p : Project.Term n) : Project.Formula.satisfies ρ (avoidFormula w b p) ↔
      Avoid (w.eval ρ) (b.eval ρ) (p.eval ρ) := by
  simp only [avoidFormula, Avoid, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, stemAvoidFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem extends_of_codes (hZF : M.Models SetTheory.ZF) {p q s S t T : M.Domain}
    (hp : KPair_d M p s S) (hq : KPair_d M q t T)
    (hpq : CodedExtends (M := M) p q) : Extends s S t T := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨s', S', t', T', hp', hq', he⟩ := hpq
  obtain ⟨es, eS⟩ := I.injective hp hp'
  obtain ⟨et, eT⟩ := I.injective hq hq'
  subst s'
  subst S'
  subst t'
  subst T'
  exact he

theorem condition_of_codes (hZF : M.Models SetTheory.ZF) {w A p s S : M.Domain}
    (hc : KPair_d M p s S) (hp : CodedCondition w A p) : Condition w A s S := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨s', S', hc', hCond⟩ := hp
  obtain ⟨es, eS⟩ := I.injective hc hc'
  subst s'
  subst S'
  exact hCond

theorem union_stems_exists (hZF : M.Models SetTheory.ZF) {w A G : M.Domain}
    (hG : Conditions w A G) : ∃ X,
      Internal.Subset M.mem X w ∧ ∀ k, M.mem k X ↔ StemMember G k := by
  let ρ : Env M 1 := ⟨fun _ => G, fun _ => w⟩
  let φ : UnarySchema 1 := { body := Syntax.stemMemberFormula (.bound 1) .newest }
  obtain ⟨X, hX⟩ := ZF.separation_exists_d hZF φ ρ w
  have hφ k : φ.denote ρ k ↔ StemMember G k :=
    Syntax.stemMemberFormula_semantics hZF.1 _ _ _
  refine ⟨X, fun k hk => ((hX k).mp hk).1, fun k => (hX k).trans ?_⟩
  change M.mem k w ∧ φ.denote ρ k ↔ _
  rw [hφ k]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨p, s, S, hp, hc, hk⟩ := h
  exact (condition_of_codes hZF hc (hG p hp)).1.1 k hk

theorem union_stems_hits (hZF : M.Models SetTheory.ZF) {w A G X a : M.Domain}
    (hw : M.IsOmega w) (hXw : Internal.Subset M.mem X w)
    (hX : ∀ k, M.mem k X ↔ StemMember G k) (ha : M.mem a A) (hHit : MeetsHit w A G) :
    Internal.InfiniteInter M.mem w a X := by
  obtain ⟨d, hd⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) a X
  have hdw : Internal.Subset M.mem d w := fun k hk => hXw k ((hd k).mp hk).2
  refine ⟨d, hd, (Internal.infinite_iff_unbounded hZF
    ((Internal.omega_native_iff hZF.1 w).mpr hw) hdw).mpr ?_⟩
  intro n hn
  obtain ⟨p, hp, s, S, hc, k, hks, hka, hnk⟩ := hHit a n ha hn
  have hkX := (hX k).mpr ⟨p, s, S, hp, hc, hks⟩
  exact ⟨k, hXw k hkX, hnk.symm, (hd k).mpr ⟨hka, hkX⟩⟩

theorem union_stems_avoids (hZF : M.Models SetTheory.ZF) {w A G X b p s S : M.Domain}
    (hG : Conditions w A G) (hDir : Directed (M := M) G)
    (hX : ∀ k, M.mem k X ↔ StemMember G k) (hp : M.mem p G)
    (hps : KPair_d M p s S) (hAvoid : StemAvoid w b s S) :
    ∀ k, M.mem k b → M.mem k X → M.mem k s := by
  intro k hkb hkX
  obtain ⟨q, t, T, hq, hqt, hkt⟩ := (hX k).mp hkX
  obtain ⟨r, hr, hrp, hrq⟩ := hDir p q hp hq
  obtain ⟨u, U, hru, hCond⟩ := hG r hr
  have hup := extends_of_codes hZF hru hps hrp
  have huq := extends_of_codes hZF hru hqt hrq
  have hku := huq.1 k hkt
  classical
  by_cases hks : M.mem k s
  · exact hks
  · exact False.elim (hup.2.2 (hAvoid u ⟨hCond.1, k, hku, hkb, hks⟩))

theorem separator_exists (hZF : M.Models SetTheory.ZF) {w A C G : M.Domain}
    (hw : M.IsOmega w) (hG : Conditions w A G) (hDir : Directed (M := M) G)
    (hHit : MeetsHit w A G) (hAvoid : MeetsAvoid w C G) :
    ∃ X, WeakSeparator w A C X := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨X, hXw, hX⟩ := union_stems_exists hZF hG
  refine ⟨X, hXw, fun a ha => union_stems_hits hZF hw hXw hX ha hHit, ?_⟩
  intro b hb
  obtain ⟨p, hp, s, S, hps, hAvoid⟩ := hAvoid b hb
  have hCond := condition_of_codes hZF hps (hG p hp)
  obtain ⟨d, hd⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) b X
  refine ⟨d, hd, (ForcingFinite.finite_correct hZF w d).mpr ?_⟩
  apply ZF.finite_subset_l I hZF ((ForcingFinite.finite_correct hZF w s).mp hCond.1.2)
  intro k hk
  obtain ⟨hkb, hkX⟩ := (hd k).mp hk
  exact union_stems_avoids hZF hG hDir hX hp hps hAvoid k hkb hkX

namespace Syntax
open Internal.Syntax

def conditionsFormula {n} (w A G : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest G.weaken) (codedConditionFormula w.weaken A.weaken .newest))

def directedFormula {n} (G : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.imp (.mem (.bound 1) G.weaken.weaken)
    (.imp (.mem .newest G.weaken.weaken)
      (.existsE (.conj (.mem .newest G.weaken.weaken.weaken)
        (.conj (codedExtendsFormula .newest (.bound 2)) (codedExtendsFormula .newest (.bound 1))))))))

def meetsHitFormula {n} (w A G : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.imp (.mem (.bound 1) A.weaken.weaken)
    (.imp (.mem .newest w.weaken.weaken)
      (.existsE (.conj (.mem .newest G.weaken.weaken.weaken)
        (hitFormula (.bound 2) (.bound 1) .newest))))))

def meetsAvoidFormula {n} (w C G : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest C.weaken)
    (.existsE (.conj (.mem .newest G.weaken.weaken) (avoidFormula w.weaken.weaken (.bound 1) .newest))))

def weakSeparatorFormula {n} (w A C X : Project.Term n) : Project.Formula 1 n :=
  .conj (SubsetFormula X w)
    (.conj (.forallE (.imp (.mem .newest A.weaken) (InfiniteInterFormula w.weaken .newest X.weaken)))
      (.forallE (.imp (.mem .newest C.weaken)
        (.existsE (.conj (InterFormula .newest (.bound 1) X.weaken.weaken)
          (FiniteFormula w.weaken.weaken .newest))))))

derive_free_closed conditionsFormula
derive_free_closed directedFormula
derive_free_closed meetsHitFormula
derive_free_closed meetsAvoidFormula
derive_free_closed weakSeparatorFormula

theorem conditionsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A G : Project.Term n) : Project.Formula.satisfies ρ (conditionsFormula w A G) ↔
      Conditions (w.eval ρ) (A.eval ρ) (G.eval ρ) := by
  simp only [conditionsFormula, Conditions, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    codedConditionFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem directedFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (G : Project.Term n) : Project.Formula.satisfies ρ (directedFormula G) ↔
      Directed (M := M) (G.eval ρ) := by
  simp only [directedFormula, Directed, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    codedExtendsFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem meetsHitFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A G : Project.Term n) : Project.Formula.satisfies ρ (meetsHitFormula w A G) ↔
      MeetsHit (w.eval ρ) (A.eval ρ) (G.eval ρ) := by
  simp only [meetsHitFormula, MeetsHit, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    hitFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem meetsAvoidFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w C G : Project.Term n) : Project.Formula.satisfies ρ (meetsAvoidFormula w C G) ↔
      MeetsAvoid (w.eval ρ) (C.eval ρ) (G.eval ρ) := by
  simp only [meetsAvoidFormula, MeetsAvoid, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    avoidFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem weakSeparatorFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A C X : Project.Term n) : Project.Formula.satisfies ρ (weakSeparatorFormula w A C X) ↔
      WeakSeparator (w.eval ρ) (A.eval ρ) (C.eval ρ) (X.eval ρ) := by
  simp only [weakSeparatorFormula, WeakSeparator, Project.Formula.satisfies_conj_iff,
    satisfies_SubsetFormula hE, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_mem_iff,
    satisfies_InfiniteInterFormula hE, Project.Formula.satisfies_exists_iff,
    satisfies_InterFormula hE, satisfies_FiniteFormula hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def separatorBody : Project.Formula 1 4 :=
  .imp (Project.Formula.isOmega (.bound 3))
    (.imp (conditionsFormula (.bound 3) (.bound 2) .newest)
      (.imp (directedFormula .newest)
        (.imp (meetsHitFormula (.bound 3) (.bound 2) .newest)
          (.imp (meetsAvoidFormula (.bound 3) (.bound 1) .newest)
            (.existsE (weakSeparatorFormula (.bound 4) (.bound 3) (.bound 2) .newest))))))

theorem separatorBody_closed : separatorBody.FreeClosed := by
  simp -implicitDefEqProofs [separatorBody, Definitional.Formula.FreeClosed]

def separatorSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose separatorBody) (ObjectTheory.universalClose_closed _ separatorBody_closed)

theorem separatorBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 4) :
    Project.Formula.satisfies ρ separatorBody := by
  simp only [separatorBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    conditionsFormula_semantics hZF.1, directedFormula_semantics hZF.1,
    meetsHitFormula_semantics hZF.1, meetsAvoidFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, weakSeparatorFormula_semantics hZF.1]
  exact fun hw hG hDir hHit hAvoid => separator_exists hZF hw hG hDir hHit hAvoid
end Syntax

theorem derives_separator : Project.Derives SetTheory.ZF Syntax.separatorSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.separatorBody (Syntax.separatorBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

import FIMADModels.DowPoset

/-! Internal dense requirements for the exact forbidden-stem forcing.
The infinitude used here is the manuscript's injection-based predicate;
all witnesses and finite stems belong to the arbitrary ZF model. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def AtLeast (n k : M.Domain) : Prop := n = k ∨ M.mem n k

theorem atLeast_trans (hZF : M.Models SetTheory.ZF) {w n m k : M.Domain}
    (hw : M.IsOmega w) (hk : M.mem k w) (hnm : AtLeast (M := M) n m)
    (hmk : AtLeast (M := M) m k) : AtLeast (M := M) n k := by
  rcases hnm with rfl | hnm
  · exact hmk
  · rcases hmk with rfl | hmk
    · exact Or.inr hnm
    · exact Or.inr ((hw.members_areOrdinals hZF k hk).transitive m hmk n hnm)

theorem finiteSubset_singleton (hZF : M.Models SetTheory.ZF) {w k t : M.Domain}
    (hw : M.IsOmega w) (hk : M.mem k w) (ht : M.IsSingletonOf t k) : FiniteSubset w t := by
  obtain ⟨n, hn, hnw⟩ := hw.1.2 k hk
  refine ⟨fun x hx => (ht x).mp hx ▸ hk, Internal.finite_of_subset_natural hZF hnw ?_⟩
  intro x hx
  have eq := (ht x).mp hx
  subst x
  exact hn.predecessor_mem

theorem finiteSubset_union (hZF : M.Models SetTheory.ZF) {w s t r : M.Domain}
    (hw : M.IsOmega w) (hs : FiniteSubset w s) (ht : FiniteSubset w t)
    (hr : M.IsUnionOfTwo r s t) : FiniteSubset w r := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  refine ⟨fun x hx => ((hr x).mp hx).elim (hs.1 x) (ht.1 x), ?_⟩
  apply (ForcingFinite.finite_correct hZF w r).mpr
  exact ZF.finite_union_l I hZF hw ((ForcingFinite.finite_correct hZF w s).mp hs.2)
    ((ForcingFinite.finite_correct hZF w t).mp ht.2) hr

def StemHit (a n s : M.Domain) : Prop :=
  ∃ k, M.mem k s ∧ M.mem k a ∧ AtLeast (M := M) n k

def Hit (a n p : M.Domain) : Prop :=
  ∃ s S, KPair_d M p s S ∧ StemHit a n s

theorem hit_extension (hZF : M.Models SetTheory.ZF) {w A a n s S : M.Domain}
    (hw : M.IsOmega w) (haA : M.mem a A) (haw : Internal.Subset M.mem a w)
    (hi : Internal.Infinite M.mem w a) (hnw : M.mem n w) (hp : Condition w A s S) :
    ∃ r, Condition w A r S ∧ Extends r S s S ∧ StemHit a n r := by
  have hw' := (Internal.omega_native_iff hZF.1 w).mpr hw
  obtain ⟨m, hmw, hm⟩ := hp.2.2.2 s hp.1 hp.2.2.1 a haA
  obtain ⟨b, hbw, hnb, hmb⟩ := natural_common_bound hZF hw' hnw hmw
  obtain ⟨k, hkw, hbk, hka⟩ :=
    (Internal.infinite_iff_unbounded hZF hw' haw).mp hi b hbw
  have hbk' : AtLeast (M := M) b k := hbk.symm
  have hmk := atLeast_trans hZF hw hkw hmb hbk'
  have hnk := atLeast_trans hZF hw hkw hnb hbk'
  obtain ⟨t, ht⟩ := KP.exists_singleton (ZF.modelsKP hZF) k
  have htf := finiteSubset_singleton hZF hw hkw ht
  have htTail : Tail w a m t := ⟨htf, fun x hx => by
    have eq := (ht x).mp hx
    subst x
    exact ⟨hka, hmk.elim (fun h => Or.inl h.symm) Or.inr⟩⟩
  obtain ⟨r, hr⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) s t
  have hrS := hm t htTail r hr
  exact ⟨r, ⟨finiteSubset_union hZF hw hp.1 htf hr, hp.2.1, hrS, hp.2.2.2⟩,
    ⟨fun x hx => (hr x).mpr (Or.inl hx), (fun _ h => h), hrS⟩,
    k, (hr k).mpr (Or.inr ((ht k).mpr rfl)), hka, hnk⟩

theorem hit_dense (hZF : M.Models SetTheory.ZF) {w A B R a n : M.Domain}
    (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (haA : M.mem a A) (haw : Internal.Subset M.mem a w)
    (hi : Internal.Infinite M.mem w a) (hnw : M.mem n w) :
    ∀ p, M.mem p B → ∃ q, M.mem q B ∧ Entry_d M q p R ∧ Hit a n q := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  intro p hp
  obtain ⟨s, S, hps, hCond⟩ := (hB p).mp hp
  obtain ⟨r, hrCond, hrs, hHit⟩ := hit_extension hZF hw haA haw hi hnw hCond
  obtain ⟨q, hq⟩ := I.total r S
  have hqB := (hB q).mpr ⟨r, S, hq, hrCond⟩
  exact ⟨q, hqB, (hR q p).mpr ⟨hqB, hp, r, S, s, S, hq, hps, hrs⟩,
    r, S, hq, hHit⟩

namespace Syntax
open Internal.Syntax

def atLeastFormula {d} (n k : Project.Term d) : Project.Formula 1 d :=
  .disj (Project.Formula.extensionalEq n k) (.mem n k)

def stemHitFormula {d} (a n s : Project.Term d) : Project.Formula 1 d :=
  .existsE (.conj (.mem .newest s.weaken)
    (.conj (.mem .newest a.weaken) (atLeastFormula n.weaken .newest)))

derive_free_closed atLeastFormula
derive_free_closed stemHitFormula

theorem stemHitFormula_semantics (hE : Extensional M) {d} (ρ : Env M d)
    (a n s : Project.Term d) : Project.Formula.satisfies ρ (stemHitFormula a n s) ↔
      StemHit (a.eval ρ) (n.eval ρ) (s.eval ρ) := by
  simp only [stemHitFormula, StemHit, atLeastFormula, AtLeast,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

/-- Object parameters w, A, a, n, s, S. -/
def hitBody : Project.Formula 1 6 :=
  .imp (Project.Formula.isOmega (.bound 5))
    (.imp (.mem (.bound 3) (.bound 4))
      (.imp (SubsetFormula (.bound 3) (.bound 5))
        (.imp (InfiniteFormula (.bound 5) (.bound 3))
          (.imp (.mem (.bound 2) (.bound 5))
            (.imp (conditionFormula (.bound 5) (.bound 4) (.bound 1) .newest)
              (.existsE (.conj (conditionFormula (.bound 6) (.bound 5) .newest (.bound 1))
                (.conj (extendsFormula .newest (.bound 1) (.bound 2) (.bound 1))
                  (stemHitFormula (.bound 4) (.bound 3) .newest)))))))))

theorem hitBody_closed : hitBody.FreeClosed := by
  simp -implicitDefEqProofs [hitBody, Definitional.Formula.FreeClosed]

def hitSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose hitBody) (ObjectTheory.universalClose_closed _ hitBody_closed)

theorem hitBody_valid (hZF : M.Models SetTheory.ZF) (ρ : Env M 6) :
    Project.Formula.satisfies ρ hitBody := by
  simp only [hitBody, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_mem_iff, satisfies_SubsetFormula hZF.1,
    satisfies_InfiniteFormula hZF.1, conditionFormula_semantics hZF.1,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    extendsFormula_semantics hZF.1, stemHitFormula_semantics hZF.1]
  exact fun hw haA haw hi hn hp => hit_extension hZF hw haA haw hi hn hp
end Syntax

theorem derives_hit_extension : Project.Derives SetTheory.ZF Syntax.hitSentence := by
  apply ObjectTheory.derives_of_native_zf_models
  intro M hZF
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.hitBody (Syntax.hitBody_valid hZF)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

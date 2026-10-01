import FIMADModels.DowNameExtension

/-! One internal countable test family controls every member of an internally
countable set of unbounded forcing names. Selection is performed inside ZFC
on a bounded set of relation/test pairs. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def NameFamilyTests (w A B R c L H : M.Domain) : Prop :=
  InternalCountable w H ∧ (∀ X, M.mem X H → Internal.Subset M.mem X w) ∧
    ∀ t, M.mem t L → ∃ E, MembershipDecisions w B R c t E ∧
      ∀ b, MeetsTests w b H → TallDensity w A E b

namespace Syntax
def selectedNameTestsFormula {n} (w A B R c t q : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m q.weaken.weaken (.bound 1) .newest)
    (.conj (membershipDecisionsFormula w.weaken.weaken B.weaken.weaken R.weaken.weaken
      c.weaken.weaken t.weaken.weaken (.bound 1))
      (tallTestsWitnessFormula w.weaken.weaken A.weaken.weaken (.bound 1) .newest))))

derive_free_closed selectedNameTestsFormula

theorem selectedNameTestsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A B R c t q : Project.Term n) : Project.Formula.satisfies ρ (selectedNameTestsFormula w A B R c t q) ↔
      ∃ E H, KPair_d M (q.eval ρ) E H ∧
        MembershipDecisions (w.eval ρ) (B.eval ρ) (R.eval ρ) (c.eval ρ) (t.eval ρ) E ∧
        TallTestsWitness (w.eval ρ) (A.eval ρ) E H := by
  simp only [selectedNameTestsFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, membershipDecisionsFormula_semantics hE,
    tallTestsWitnessFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem bounded_membership_decisions_exists (hZF : M.Models SetTheory.ZF)
    {w B R c t P : M.Domain}
    (hP : M.IsCartesianProduct
      (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) P B w) :
    ∃ E, MembershipDecisions w B R c t E ∧ Internal.Subset M.mem E P := by
  obtain ⟨F, hF⟩ := membership_decisions_exists hZF w B R c t
  obtain ⟨E, hE⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) F P
  refine ⟨E, ?_, fun x hx => ((hE x).mp hx).2⟩
  intro p k
  constructor
  · rintro ⟨x, hxp, hxE⟩
    exact (hF p k).mp ⟨x, hxp, ((hE x).mp hxE).1⟩
  · intro h
    obtain ⟨x, hx, hxF⟩ := (hF p k).mpr h
    exact ⟨x, hx, (hE x).mpr ⟨hxF, (hP x).mpr ⟨p, h.1, k, h.2.1, hx⟩⟩⟩

theorem countable_name_tests_exists (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W L : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hLc : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t ∧ ForcesUnboundedName B R W t) :
    ∃ H, InternalCountable w H ∧ (∀ X, M.mem X H → Internal.Subset M.mem X w) ∧
      ∀ t, M.mem t L → ∃ E, MembershipDecisions w B R c t E ∧
        ∀ b, MeetsTests w b H → TallDensity w A E b := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B w
  obtain ⟨PE, hPE⟩ := ZF.exists_powerSet hZF P
  obtain ⟨Pw, hPw⟩ := ZF.exists_powerSet hZF w
  obtain ⟨PH, hPH⟩ := ZF.exists_powerSet hZF Pw
  obtain ⟨Q, hQ⟩ := ZF.exists_cartesianProduct hZF I PE PH
  let ρ : Env M 5 := ((((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push B).push R).push c
  let φ : BinarySchema 5 := {
    body := Syntax.selectedNameTestsFormula (.bound 6) (.bound 5) (.bound 4) (.bound 3)
      (.bound 2) (.bound 1) .newest }
  have hφ t q : φ.denote ρ t q ↔ ∃ E H, KPair_d M q E H ∧
      MembershipDecisions w B R c t E ∧ TallTestsWitness w A E H :=
    Syntax.selectedNameTestsFormula_semantics hZF.1 _ _ _ _ _ _ _ _
  obtain ⟨G, hG, he⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (X := L) (Y := Q) (by
    intro t htL
    obtain ⟨ht, hForce⟩ := hNames t htL
    obtain ⟨E, hE, hEP⟩ := bounded_membership_decisions_exists (R := R) (c := c) (t := t) hZF hP
    obtain ⟨H, hH⟩ := tall_tests_exists hZFC hw
      (membership_decisions_unbounded hZF O hB hR hc hTop ht hW hE hForce)
      (membership_decisions_monotone hZF O hB hR hE)
    obtain ⟨q, hq⟩ := I.total E H
    exact ⟨q, (hQ q).mpr ⟨E, (hPE E).mpr hEP, H,
      (hPH H).mpr (fun X hX => (hPw X).mpr (hH.2.1 X hX)), hq⟩,
      (hφ t q).mpr ⟨E, H, hq, hE, hH⟩⟩)
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : BinarySchema 1 := {
    body := Syntax.selectedFamilyFormula (.bound 2) (.bound 1) .newest }
  have hψ t H : ψ.denote η t H ↔ ∃ q E, Entry_d M t q G ∧ KPair_d M q E H :=
    Syntax.selectedFamilyFormula_semantics hZF.1 _ _ _ _
  have unique {t q E H q' E' H'} (htq : Entry_d M t q G) (htq' : Entry_d M t q' G)
      (hq : KPair_d M q E H) (hq' : KPair_d M q' E' H') : E = E' ∧ H = H' :=
    I.injective hq ((hG.1.2 t q' q htq' htq) ▸ hq')
  obtain ⟨C, hC, hCc⟩ := countable_test_image hZFC ψ η hLc (by
    intro t ht
    obtain ⟨q, _, htq⟩ := hG.2.2 t ht
    obtain ⟨E, H, hq, _, _⟩ := (hφ t q).mp (he t q htq)
    exact ⟨H, (hψ t H).mpr ⟨q, E, htq, hq⟩⟩) (by
      intro t _ H H' hH hH'
      obtain ⟨q, E, htq, hq⟩ := (hψ t H).mp hH
      obtain ⟨q', E', htq', hq'⟩ := (hψ t H').mp hH'
      exact (unique htq htq' hq hq').2)
  have family {F} (hF : M.mem F C) : ∃ E, TallTestsWitness w A E F := by
    obtain ⟨t, _, htF⟩ := (hC F).mp hF
    obtain ⟨q, E, htq, hq⟩ := (hψ t F).mp htF
    obtain ⟨E', F', hq', _, hF'⟩ := (hφ t q).mp (he t q htq)
    obtain ⟨rfl, rfl⟩ := I.injective hq hq'
    exact ⟨E, hF'⟩
  obtain ⟨H, hH⟩ := KP.exists_union (ZF.modelsKP hZF) C
  have hHc : InternalCountable w H := (countable_native_iff hZF w H).mpr
    (ZFC.countable_union_l I hZFC hw ((countable_native_iff hZF w C).mp hCc) hH
      (fun F hF => (family hF).elim fun _ ht => (countable_native_iff hZF w F).mp ht.1))
  refine ⟨H, hHc, ?_, ?_⟩
  · intro X hX
    obtain ⟨F, hFC, hXF⟩ := (hH X).mp hX
    obtain ⟨_, ht⟩ := family hFC
    exact ht.2.1 X hXF
  · intro t htL
    obtain ⟨q, _, htq⟩ := hG.2.2 t htL
    obtain ⟨E, F, hq, hE, hTest⟩ := (hφ t q).mp (he t q htq)
    have hFC := (hC F).mpr ⟨t, htL, (hψ t F).mpr ⟨q, E, htq, hq⟩⟩
    exact ⟨E, hE, fun b hb => hTest.2.2 b (fun X hXF =>
      hb X ((hH X).mpr ⟨F, hFC, hXF⟩))⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

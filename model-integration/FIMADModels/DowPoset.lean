import FIMADModels.FiniteStems
import YesMetaZFC.Model.Forcing.CCC.Syntax
import YesMetaZFC.Model.Forcing.TwoStep.Basic

/-! Actual internal Dow carrier, strengthening relation and CCC theorem.
The conditions use Kuratowski pairs of a finite stem and an arbitrary set of
forbidden finite stems. The final existential construction is an original ZFC
derivation. No generic filter or splitting preservation is asserted here. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def CodedCondition (w A p : M.Domain) : Prop :=
  ∃ s S, KPair_d M p s S ∧ Condition w A s S

def CodedExtends (p q : M.Domain) : Prop :=
  ∃ s S t T, KPair_d M p s S ∧ KPair_d M q t T ∧ Extends s S t T

namespace Syntax
def codedConditionFormula {n} (w A p : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m p.weaken.weaken (.bound 1) .newest)
    (conditionFormula w.weaken.weaken A.weaken.weaken (.bound 1) .newest)))

def codedExtendsFormula {n} (p q : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (kpair_m p.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
      (.conj (kpair_m q.weaken.weaken.weaken.weaken (.bound 1) .newest)
        (extendsFormula (.bound 3) (.bound 2) (.bound 1) .newest))))))

derive_free_closed codedConditionFormula
derive_free_closed codedExtendsFormula

theorem codedConditionFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A p : Project.Term n) : Project.Formula.satisfies ρ (codedConditionFormula w A p) ↔
      CodedCondition (w.eval ρ) (A.eval ρ) (p.eval ρ) := by
  simp only [codedConditionFormula, CodedCondition, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, conditionFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem codedExtendsFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (p q : Project.Term n) : Project.Formula.satisfies ρ (codedExtendsFormula p q) ↔
      CodedExtends (M := M) (p.eval ρ) (q.eval ρ) := by
  simp only [codedExtendsFormula, CodedExtends, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE, extendsFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl
end Syntax

theorem coded_extends_refl {w A p : M.Domain}
    (hp : CodedCondition w A p) : CodedExtends (M := M) p p := by
  obtain ⟨s, S, hc, hp⟩ := hp
  exact ⟨s, S, s, S, hc, hc, fun _ h => h, (fun _ h => h), hp.2.2.1⟩

theorem coded_extends_trans (hZF : M.Models SetTheory.ZF) {p q r : M.Domain}
    (hpq : CodedExtends (M := M) p q) (hqr : CodedExtends (M := M) q r) :
    CodedExtends (M := M) p r := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨s, S, t, T, hp, hq, hst, hST, hsT⟩ := hpq
  obtain ⟨t', T', v, V, hq', hr, htv, hTV, htV⟩ := hqr
  obtain ⟨eqt, eqT⟩ := I.injective hq hq'
  subst t'
  subst T'
  exact ⟨s, S, v, V, hp, hr, (fun x hx => hst x (htv x hx)),
    (fun x hx => hST x (hTV x hx)), fun h => hsT (hTV s h)⟩

theorem carrier_exists (hZF : M.Models SetTheory.ZF) (w A : M.Domain) :
    ∃ B, ∀ p, M.mem p B ↔ CodedCondition w A p := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨W, hW⟩ := ZF.exists_powerSet hZF w
  let ρ : Env M 1 := ⟨fun _ => w, fun _ => w⟩
  let φ : UnarySchema 1 := {
    body := Syntax.finiteSubsetFormula (.bound 1) .newest
    freeClosed := Syntax.finiteSubsetFormula_closed _ _ rfl rfl }
  obtain ⟨P, hP⟩ := ZF.separation_exists_d hZF φ ρ W
  have hp X : M.mem X P ↔ FiniteSubset w X := by
    rw [hP X]
    have hSat := Syntax.finiteSubsetFormula_semantics hZF.1 (ρ.push X) (.bound 1) .newest
    change M.mem X W ∧ Project.Formula.satisfies (ρ.push X) φ.body ↔ _
    rw [show Project.Formula.satisfies (ρ.push X) φ.body ↔ FiniteSubset w X from hSat]
    exact ⟨And.right, fun h => ⟨(hW X).mpr h.1, h⟩⟩
  obtain ⟨Q, hQ⟩ := ZF.exists_powerSet hZF P
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I P Q
  let η : Env M 2 := ρ.push A
  let ψ : UnarySchema 2 := {
    body := Syntax.codedConditionFormula (.bound 2) (.bound 1) .newest }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF ψ η D
  have hψ p : ψ.denote η p ↔ CodedCondition w A p :=
    Syntax.codedConditionFormula_semantics hZF.1 _ _ _ _
  refine ⟨B, fun p => (hB p).trans ?_⟩
  change M.mem p D ∧ ψ.denote η p ↔ CodedCondition w A p
  rw [hψ p]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨s, S, hc, hs, hS, _⟩ := h
  exact (hD p).mpr ⟨s, (hp s).mpr hs, S,
    (hQ S).mpr (fun t ht => (hp t).mpr (hS t ht)), hc⟩

theorem order_exists (hZF : M.Models SetTheory.ZF) (w A : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ CodedCondition w A p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q) ∧
    Cond_order_d M B R B := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, hB⟩ := carrier_exists hZF w A
  let φ : BinarySchema 0 := { body := Syntax.codedExtendsFormula (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => w⟩
  obtain ⟨R, _, hR⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ B
  have hr p q : Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q := by
    rw [show Entry_d M p q R ↔ M.PairMember I p q R from Iff.rfl, hR p q]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    exact Syntax.codedExtendsFormula_semantics hZF.1 _ _ _
  refine ⟨B, R, hB, hr, {
    refl := fun p hp => (hr p p).mpr ⟨hp, hp, coded_extends_refl ((hB p).mp hp)⟩
    trans := fun p q r hp hq hrr hpq hqr => (hr p r).mpr
      ⟨hp, hrr, coded_extends_trans hZF ((hr p q).mp hpq).2.2 ((hr q r).mp hqr).2.2⟩
    zero := fun p _ hz => False.elim
      (KP.mem_irrefl_d (ZF.modelsKP hZF) B ((hr p B).mp hz).2.1) }⟩

theorem dow_ccc (hZFC : M.Models SetTheory.ZFC) {w A B R : M.Domain} (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q) :
    Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) w B R B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP, hcP⟩ := FiniteStems.finite_stem_space hZFC hw
  intro C hC
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => w⟩
  let φ : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  have hφ p s : φ.denote ρ p s ↔ ∃ S, KPair_d M p s S := by
    simp only [BinarySchema.denote, φ, Project.Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]
    rfl
  obtain ⟨J, hJ⟩ := ZF.exists_setInjectionFromTo_of_denote hZF I φ ρ
    (source := C) (target := P) (by
      intro p hp
      obtain ⟨s, S, hc, _⟩ := (hB p).mp (hC.1 p hp).1
      exact ⟨s, (hφ p s).mpr ⟨S, hc⟩⟩) (by
      intro p _ s t hs ht
      obtain ⟨S, hs⟩ := (hφ p s).mp hs
      obtain ⟨T, ht⟩ := (hφ p t).mp ht
      exact (I.injective hs ht).1) (by
      intro p s hp hs
      obtain ⟨S, hs⟩ := (hφ p s).mp hs
      obtain ⟨t, T, ht, hCond⟩ := (hB p).mp (hC.1 p hp).1
      obtain ⟨eqs, _⟩ := I.injective hs ht
      subst t
      exact (hP s).mpr hCond.1) (by
      intro p q s hp hq hps hqs
      obtain ⟨S, hps⟩ := (hφ p s).mp hps
      obtain ⟨T, hqs⟩ := (hφ q s).mp hqs
      obtain ⟨sp, Sp, hcp, hCondp⟩ := (hB p).mp (hC.1 p hp).1
      obtain ⟨sq, Sq, hcq, hCondq⟩ := (hB q).mp (hC.1 q hq).1
      obtain ⟨esp, eSp⟩ := I.injective hps hcp
      obtain ⟨esq, eSq⟩ := I.injective hqs hcq
      subst sp
      subst Sp
      subst sq
      subst Sq
      obtain ⟨U, _, hCondU, hUS, hUT⟩ := same_stem_merge hZF
        ((Internal.omega_native_iff hZF.1 w).mpr hw) hCondp hCondq
      obtain ⟨r, hcr⟩ := I.total s U
      have hrB := (hB r).mpr ⟨s, U, hcr, hCondU⟩
      exact hC.2 p q hp hq ⟨r,
        ⟨hrB, fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hrB),
          (hR r p).mpr ⟨hrB, (hC.1 p hp).1, s, U, s, S, hcr, hps, hUS⟩⟩,
        (hR r q).mpr ⟨hrB, (hC.1 q hq).1, s, U, s, T, hcr, hqs, hUT⟩⟩)
  obtain ⟨K, hK⟩ := hcP
  exact ZF.exists_compositionInjection hZF I hJ hK

theorem top_exists (hZF : M.Models SetTheory.ZF) {w A B R : M.Domain} (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q) :
    ∃ e, M.mem e B ∧ ∀ p, M.mem p B → Entry_d M p e R := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨E, hE, hEw⟩ := hw.1.1
  have hFinite : FiniteSubset w E := ⟨fun x hx => (hE x hx).elim,
    Internal.finite_of_subset_natural hZF hEw (fun _ hx => hx)⟩
  have hCond : Condition w A E E := ⟨hFinite, (fun x hx => (hE x hx).elim),
    hE E, fun _ _ _ _ _ => ⟨E, hEw, fun _ _ r _ => hE r⟩⟩
  obtain ⟨e, he⟩ := I.total E E
  have heB := (hB e).mpr ⟨E, E, he, hCond⟩
  refine ⟨e, heB, fun p hp => ?_⟩
  obtain ⟨s, S, hps, _⟩ := (hB p).mp hp
  exact (hR p e).mpr ⟨hp, heB, s, S, E, E, hps, he,
    (fun x hx => (hE x hx).elim), (fun x hx => (hE x hx).elim), hE s⟩

namespace Syntax
def carrierFormula {n} (w A B : Project.Term n) : Project.Formula 1 n :=
  .forallE (.iff (.mem .newest B.weaken) (codedConditionFormula w.weaken A.weaken .newest))

def orderFormula {n} (B R : Project.Term n) : Project.Formula 1 n :=
  .forallE (.forallE (.iff (entry_m (.bound 1) .newest R.weaken.weaken)
    (.conj (.mem (.bound 1) B.weaken.weaken)
      (.conj (.mem .newest B.weaken.weaken) (codedExtendsFormula (.bound 1) .newest)))))

derive_free_closed carrierFormula
derive_free_closed orderFormula

def topFormula {n} (B R e : Project.Term n) : Project.Formula 1 n :=
  .conj (.mem e B) (.forallE (.imp (.mem .newest B.weaken) (entry_m .newest e.weaken R.weaken)))

derive_free_closed topFormula

theorem carrierFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w A B : Project.Term n) : Project.Formula.satisfies ρ (carrierFormula w A B) ↔
      ∀ p, M.mem p (B.eval ρ) ↔ CodedCondition (w.eval ρ) (A.eval ρ) p := by
  simp only [carrierFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    codedConditionFormula_semantics hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

theorem orderFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R : Project.Term n) : Project.Formula.satisfies ρ (orderFormula B R) ↔
      ∀ p q, Entry_d M p q (R.eval ρ) ↔
        M.mem p (B.eval ρ) ∧ M.mem q (B.eval ρ) ∧ CodedExtends (M := M) p q := by
  simp only [orderFormula, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_conj_iff, entry_sat_l M hE, codedExtendsFormula_semantics hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

theorem topFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R e : Project.Term n) : Project.Formula.satisfies ρ (topFormula B R e) ↔
      M.mem (e.eval ρ) (B.eval ρ) ∧ ∀ p, M.mem p (B.eval ρ) →
        Entry_d M p (e.eval ρ) (R.eval ρ) := by
  simp only [topFormula, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

def existsCCCBody : Project.Formula 1 2 :=
  .imp (Project.Formula.isOmega (.bound 1))
    (.existsE (.existsE (.existsE (.conj (carrierFormula (.bound 4) (.bound 3) (.bound 2))
      (.conj (orderFormula (.bound 2) (.bound 1))
        (.conj (cond_order_m (.bound 2) (.bound 1) (.bound 2))
          (.conj (ccc_m kpair_convention_l (.bound 4) (.bound 2) (.bound 1) (.bound 2))
            (topFormula (.bound 2) (.bound 1) .newest))))))))

theorem existsCCCBody_closed : existsCCCBody.FreeClosed := by
  simp -implicitDefEqProofs [existsCCCBody, Definitional.Formula.FreeClosed]

def existsCCCSentence : Project.Sentence := Project.Sentence.ofFormula
  (ObjectTheory.universalClose existsCCCBody)
  (ObjectTheory.universalClose_closed _ existsCCCBody_closed)

theorem existsCCCBody_valid (hZFC : M.Models SetTheory.ZFC) (ρ : Env M 2) :
    Project.Formula.satisfies ρ existsCCCBody := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  simp only [existsCCCBody, Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, carrierFormula_semantics hZF.1,
    orderFormula_semantics hZF.1, cond_order_sat_l hZF.1, ccc_sat_l I hZF.1,
    topFormula_semantics hZF.1]
  intro hw
  obtain ⟨B, R, hB, hR, hOrder⟩ := order_exists hZF (ρ.bound 1) (ρ.bound 0)
  obtain ⟨e, he, hTop⟩ := top_exists hZF hw hB hR
  exact ⟨B, R, e, hB, hR, hOrder, dow_ccc hZFC hw hB hR, he, hTop⟩
end Syntax

/-- ZFC constructs the exact Dow forcing and proves its internal CCC. -/
theorem derives_dow_poset_ccc : Project.Derives SetTheory.ZFC Syntax.existsCCCSentence := by
  apply ObjectTheory.derives_of_native_zfc_models
  intro M hZFC
  rw [SetTheory.Structure.satisfiesSentence_iff]
  exact ObjectTheory.universalClose_valid Syntax.existsCCCBody (Syntax.existsCCCBody_valid hZFC)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

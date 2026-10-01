import FIMADModels.DowTallness
import FIMADModels.CheckDecisions

/-! Real internal forcing names supply the decision-relation hypotheses of
the Dow tallness theorem. Membership decisions are an actual separated graph
on the internal condition carrier times omega, using the forcing translation.
-/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def MembershipDecisions (w B R c t E : M.Domain) : Prop :=
  ∀ p k, Entry_d M p k E ↔ M.mem p B ∧ M.mem k w ∧
    ∃ sk, Check_d M c k sk ∧ Mem_force_d M B R B p sk t

namespace Syntax
def membershipDecisionFormula {n} (B R c t p k : Project.Term n) : Project.Formula 1 n :=
  .existsE (.conj (check_m c.weaken k.weaken .newest)
    (mem_force_m B.weaken R.weaken B.weaken p.weaken .newest t.weaken))

def nameTailFormula {n} (W t N : Project.Term n) : Project.Formula 1 n :=
  .existsE (.conj (.mem .newest W.weaken)
    (.conj (atLeastFormula N.weaken .newest) (.mem .newest t.weaken)))

def unboundedNameFormula {n} (W t : Project.Term n) : Project.Formula 1 n :=
  .forallE (.imp (.mem .newest W.weaken) (nameTailFormula W.weaken t.weaken .newest))

derive_free_closed membershipDecisionFormula
derive_free_closed nameTailFormula
derive_free_closed unboundedNameFormula

theorem membershipDecisionFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (B R c t p k : Project.Term n) : Project.Formula.satisfies ρ (membershipDecisionFormula B R c t p k) ↔
      ∃ sk, Check_d M (c.eval ρ) (k.eval ρ) sk ∧
        Mem_force_d M (B.eval ρ) (R.eval ρ) (B.eval ρ) (p.eval ρ) sk (t.eval ρ) := by
  simp only [membershipDecisionFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, check_sat_l M hE, mem_force_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax

theorem membership_decisions_exists (hZF : M.Models SetTheory.ZF) (w B R c t : M.Domain) :
    ∃ E, MembershipDecisions w B R c t E := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨P, hP⟩ := ZF.exists_cartesianProduct hZF I B w
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push c).push t
  let φ : BinarySchema 4 := {
    body := Syntax.membershipDecisionFormula (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ p k : φ.denote ρ p k ↔ ∃ sk, Check_d M c k sk ∧ Mem_force_d M B R B p sk t :=
    Syntax.membershipDecisionFormula_semantics hZF.1 _ _ _ _ _ _ _
  obtain ⟨E, hE⟩ := ZF.separation_exists_d hZF (UnarySchema.relationMember kpair_convention_l φ) ρ P
  have he x : M.mem x E ↔ ∃ p k, M.mem p B ∧ M.mem k w ∧ KPair_d M x p k ∧
      ∃ sk, Check_d M c k sk ∧ Mem_force_d M B R B p sk t := by
    rw [hE x, hP x, Project.Formula.satisfies_relationMember_iff I φ ρ x]
    constructor
    · rintro ⟨⟨p, hp, k, hk, hcode⟩, p', k', hcode', hφ'⟩
      obtain ⟨rfl, rfl⟩ := I.injective hcode hcode'
      exact ⟨p, k, hp, hk, hcode, (hφ p k).mp hφ'⟩
    · rintro ⟨p, k, hp, hk, hcode, hpk⟩
      exact ⟨⟨p, hp, k, hk, hcode⟩, p, k, hcode, (hφ p k).mpr hpk⟩
  refine ⟨E, fun p k => ?_⟩
  constructor
  · rintro ⟨x, hx, hxE⟩
    obtain ⟨p', k', hp', hk', hx', hpk⟩ := (he x).mp hxE
    obtain ⟨rfl, rfl⟩ := I.injective hx hx'
    exact ⟨hp', hk', hpk⟩
  · rintro ⟨hp, hk, hpk⟩
    obtain ⟨x, hx⟩ := I.total p k
    exact ⟨x, hx, (he x).mpr ⟨p, k, hp, hk, hx, hpk⟩⟩

theorem membership_decisions_monotone (hZF : M.Models SetTheory.ZF)
    {w A B R c t E : M.Domain} (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hE : MembershipDecisions w B R c t E) : MonotoneDecisions w A E := by
  intro p q k hp hq hqp hpk
  obtain ⟨hpB, hk, sk, hsk, hForce⟩ := (hE p k).mp hpk
  have hqB := (hB q).mpr hq
  have hqz : q ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hqB)
  exact (hE q k).mpr ⟨hqB, hk, sk, hsk, (regular_mem_l O sk t).1 p q hpB
    ⟨hqB, hqz, (hR q p).mpr ⟨hqB, hpB, hqp⟩⟩ hForce⟩

theorem membership_decisions_unbounded (hZF : M.Models SetTheory.ZF)
    {w A B R c t W E : M.Domain} (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (ht : Name_d M B t) (hW : Check_d M c w W)
    (hE : MembershipDecisions w B R c t E)
    (hForce : ∀ p, M.mem p B → Forces_d M B R B
      (Syntax.unboundedNameFormula (.bound 1) .newest)
      ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p) : UnboundedDecisions w A E := by
  intro p N hp hN
  have hpB := (hB p).mpr hp
  have hpz : p ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hpB)
  have hpc : Below_d M B R B p c := ⟨hpB, hpz, hTop p hpB⟩
  obtain ⟨sn, hsn, hsnN, _⟩ := zf_check_l M hZF hc N
  have hWN := check_name_l M (check_range_l M hZF) hc hW
  let ρ : Env M 3 := ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t).push sn
  have hρ : ∀ v : Project.Term 3, Name_d M B (v.eval ρ) := by
    intro v
    cases v with
    | free _ => exact ht
    | bound i => exact Fin.cases hsnN (Fin.cases ht (fun _ => hWN)) i
  let φ : UnarySchema 3 := {
    body := .conj (Syntax.atLeastFormula (.bound 1) .newest) (.mem .newest (.bound 2)) }
  have hImp : Forces_d M B R B (.imp (.mem .newest (.bound 2))
      (Syntax.nameTailFormula (.bound 2) (.bound 1) .newest)) ρ p :=
    (forces_all_l hZF.1 _ _ p).mp (hForce p hpB) sn hsnN
  have hMem : Forces_d M B R B (.mem .newest (.bound 2) : Project.Formula 1 3) ρ p :=
    (forces_mem_l hZF.1 _ _ _ p).mpr (check_mem_force_l O hZF hc hsn hW hpB (hTop p hpB) hN)
  have hExists := forces_mp_l hZF.1
    (forces_regular_l O hZF (.mem .newest (.bound 2) : Project.Formula 1 3) ρ hρ).1
    (forces_regular_l O hZF (Syntax.nameTailFormula (.bound 2) (.bound 1) .newest) ρ hρ)
    hpB hpz hImp hMem
  obtain ⟨q, hqp, k, sk, hk, hsk, hφ⟩ := canonical_bounded_witness O hZF hc hW hpc φ ρ hρ
    (.bound 2) rfl hExists p (below_refl_l O hpB hpz)
  obtain ⟨hGe, hMem⟩ := (forces_conj_l _ _ _ q).mp hφ
  have hNk : AtLeast (M := M) N k := check_atLeast_reflect O hZF hc hsn hsk
    (below_trans_l O hc hqp hpc) (ρ.push sk) (.bound 1) .newest rfl rfl hGe
  have hMem : Mem_force_d M B R B q sk t := (forces_mem_l hZF.1 _ _ _ q).mp hMem
  exact ⟨q, k, (hB q).mp hqp.1, ((hR q p).mp hqp.2.2).2.2,
    hk, hNk, (hE q k).mpr ⟨hqp.1, hk, sk, hsk, hMem⟩⟩

theorem name_tall_tests_exists (hZFC : M.Models SetTheory.ZFC)
    {w A B R c t W : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (ht : Name_d M B t) (hW : Check_d M c w W)
    (hForce : ∀ p, M.mem p B → Forces_d M B R B
      (Syntax.unboundedNameFormula (.bound 1) .newest)
      ((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t) p) :
    ∃ E H, MembershipDecisions w B R c t E ∧ TallTestsWitness w A E H := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨E, hE⟩ := membership_decisions_exists hZF w B R c t
  obtain ⟨H, hH⟩ := tall_tests_exists hZFC hw
    (membership_decisions_unbounded hZF O hB hR hc hTop ht hW hE hForce)
    (membership_decisions_monotone hZF O hB hR hE)
  exact ⟨E, H, hE, hH⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

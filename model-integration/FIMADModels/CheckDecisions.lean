import FIMADModels.DowValueTails
import YesMetaZFC.Model.Forcing.Internal.Check.Relation
import YesMetaZFC.Model.Forcing.Internal.Forcing.Congruence

/-! Canonical ground witnesses for bounded forcing quantifiers. The proofs
use the public internal check-name construction and local forced equality;
no external valuation by well-founded recursion is used. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem check_atLeast_reflect (O : Cond_order_d M B R z) (hZF : M.Models SetTheory.ZF)
    {c N k sn sk p : M.Domain} (hc : M.mem c B)
    (hN : Check_d M c N sn) (hk : Check_d M c k sk)
    (hp : Below_d M B R z p c) {n} (ρ : Env M n) (s t : Project.Term n)
    (hs : s.eval ρ = sn) (ht : t.eval ρ = sk)
    (h : Forces_d M B R z (Syntax.atLeastFormula s t) ρ p) : AtLeast (M := M) N k := by
  classical
  apply Classical.byContradiction
  intro hNo
  have hEq : Neg_d M B R z (Forces_d M B R z (Project.Formula.extensionalEq s t) ρ) p := by
    intro q hq he
    have he : Eq_force_d M B R z q sn sk := by
      simpa only [Forces_d, Project.Formula.extensionalEq, force_code_m,
        code_eq_l M hZF.1, Project.Formula.pairArguments_get_zero,
        Project.Formula.pairArguments_get_one, hs, ht] using he
    exact hNo (Or.inl (check_force_reflect_l O hZF hc hN hk (below_trans_l O hc hq hp) he))
  have hMem : Neg_d M B R z (Forces_d M B R z (.mem s t : Project.Formula 1 n) ρ) p := by
    intro q hq hm
    have hm : Mem_force_d M B R z q sn sk := by
      simpa only [hs, ht] using (forces_mem_l hZF.1 s t ρ q).mp hm
    exact hNo (Or.inr (check_mem_reflect_l O hZF hc hN hk (below_trans_l O hc hq hp) hm))
  have h := (forces_neg_l hZF.1 _ ρ p).mp
    ((forces_disj_l (Project.Formula.extensionalEq s t) (.mem s t) ρ p).mp h)
  exact h p (below_refl_l O hp.1 hp.2.1) ((forces_conj_l _ _ _ p).mpr
    ⟨(forces_neg_l hZF.1 _ ρ p).mpr hEq, (forces_neg_l hZF.1 _ ρ p).mpr hMem⟩)

theorem canonical_bounded_witness (O : Cond_order_d M B R z) (hZF : M.Models SetTheory.ZF)
    {c w W p : M.Domain} (hc : M.mem c B) (hW : Check_d M c w W)
    (_hp : Below_d M B R z p c) {n} (φ : UnarySchema n) (ρ : Env M n)
    (hρ : ∀ v : Project.Term n, Name_d M B (v.eval ρ))
    (t : Project.Term n) (ht : t.eval ρ = W)
    (h : Forces_d M B R z (.existsE (.conj (.mem .newest t.weaken) φ.body)) ρ p) :
    Dense_d M B R z (fun q => ∃ k sk, M.mem k w ∧ Check_d M c k sk ∧
      Forces_d M B R z φ.body (ρ.push sk) q) p := by
  intro q hq
  obtain ⟨r, hr, x, hx, hrx⟩ := forces_exists_dense_l hZF.1 h q hq
  obtain ⟨hm, hφ⟩ := (forces_conj_l _ _ _ r).mp hrx
  have hm : Mem_force_d M B R z r x W := by
    simpa only [Definitional.Term.eval_newest, Definitional.Term.eval_weaken, ht] using
      (forces_mem_l hZF.1 _ _ _ r).mp hm
  obtain ⟨v, sk, b, hv, hskb, _, heq⟩ := hm.2 r (below_refl_l O hr.1 hr.2.1)
  obtain ⟨_, k, hk, hsk⟩ := (check_entry_l M hZF.1 (check_ind_l M hZF)
    (KP.exists_pair (ZF.modelsKP hZF)) hW sk b).mp hskb
  have hPush : ∀ t : Project.Term (n + 1), Name_d M B (t.eval (ρ.push x)) := by
    intro t
    cases t with
    | free i => exact hρ (.free i)
    | bound i => exact Fin.cases hx (fun i => hρ (.bound i)) i
  have hφv := (forces_regular_l O hZF φ.body (ρ.push x) hPush).1 r v hr.1 hv hφ
  have hvp := below_trans_l O hq.1 hv hr
  have hskN := check_name_l M (check_range_l M hZF) hc hsk
  exact ⟨v, hvp, k, sk, hk, hsk,
    (forces_name_congr_l O hZF φ ρ (fun i => hρ (.bound i)) hx hskN hv.1 hv.2.1 heq).mp hφv⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

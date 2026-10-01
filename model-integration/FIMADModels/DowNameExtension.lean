import FIMADModels.DowNameTheorem
import FIMADModels.DowExtension

/-! Countable tallness tests have their asserted consequence in the actual
internal generic quotient, using its own omega and injection-based infinitude.
-/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

namespace Syntax
def hitsDecisionFormula {n} (w E b N p : Project.Term n) : Project.Formula 1 n :=
  .existsE (.conj (.mem .newest w.weaken)
    (.conj (.mem .newest b.weaken) (.conj (atLeastFormula N.weaken .newest)
      (entry_m p.weaken .newest E.weaken))))
derive_free_closed hitsDecisionFormula

theorem hitsDecisionFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (w E b N p : Project.Term n) : Project.Formula.satisfies ρ (hitsDecisionFormula w E b N p) ↔
      ∃ k, M.mem k (w.eval ρ) ∧ M.mem k (b.eval ρ) ∧ AtLeast (M := M) (N.eval ρ) k ∧
        Entry_d M (p.eval ρ) k (E.eval ρ) := by
  simp only [hitsDecisionFormula, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff,
    atLeastFormula_semantics hE, entry_sat_l M hE,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
end Syntax

theorem generic_meets_decision (hZF : M.Models SetTheory.ZF) {w A B R E b N : M.Domain}
    {U : M.Domain → Prop} (hU : Generic_d M B R B U)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hDense : TallDensity w A E b) (hN : M.mem N w) :
    ∃ p k, U p ∧ M.mem k w ∧ M.mem k b ∧ AtLeast (M := M) N k ∧ Entry_d M p k E := by
  let ρ : Env M 4 := (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push E).push b).push N
  let φ : UnarySchema 4 := {
    body := Syntax.hitsDecisionFormula (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  have hd p : M.mem p D ↔ M.mem p B ∧ ∃ k,
      M.mem k w ∧ M.mem k b ∧ AtLeast (M := M) N k ∧ Entry_d M p k E := by
    rw [hD p]
    exact and_congr_right fun _ => Syntax.hitsDecisionFormula_semantics hZF.1 _ _ _ _ _ _
  obtain ⟨p, hp⟩ := hU.inhabited
  obtain ⟨q, hq, hqd⟩ := hU.meets p hp D (fun r hr => by
    obtain ⟨s, k, hs, hsr, hkb, hkw, hNk, hsk⟩ := hDense r N ((hB r).mp hr.1) hN
    have hsB := (hB s).mpr hs
    have hsz : s ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hsB)
    exact ⟨s, ⟨hsB, hsz, (hR s r).mpr ⟨hsB, hr.1, hsr⟩⟩,
      (hd s).mpr ⟨hsB, k, hkw, hkb, hNk, hsk⟩⟩)
  obtain ⟨_, k, hk⟩ := (hd q).mp hqd
  exact ⟨q, k, hq, hk⟩

theorem name_intersection_in_extension (hZF : M.Models SetTheory.ZF)
    {w A B R c t E H b : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U) (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hE : MembershipDecisions w B R c t E) (hTests : TallTestsWitness w A E H)
    (hb : Internal.Subset M.mem b w) (hbTests : MeetsTests w b H)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a))
    {T : (extension_l M hZF B R B U).Domain} (hT : Qval_d M B R B U t T) :
    Internal.InfiniteInter (extension_l M hZF B R B U).mem (e w) T (e b) := by
  let K := extension_l M hZF B R B U
  have hK : K.Models SetTheory.ZF := preserves_zf_l O hZF hU
  have mem_image {a k} (hk : M.mem k a) : K.mem (e k) (e a) :=
    (he a (e k)).mpr ⟨k, hk, rfl⟩
  have hwK : K.IsOmega (e w) := image_omega_l (hEN := hK.1) e hi he hZF
    (internal_foundation_l O hZF hU) hw
    (fun X => KP.difference_exists_d (ZF.modelsKP hK) X (e w))
  obtain ⟨d, hd⟩ := KP.intersection_exists_d (ZF.modelsKP hK) T (e b)
  have hdw : Internal.Subset K.mem d (e w) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := (he b y).mp ((hd y).mp hy).2
    exact mem_image (hb k hk)
  refine ⟨d, hd, (Internal.infinite_iff_unbounded hK
    ((Internal.omega_native_iff hK.1 (e w)).mpr hwK) hdw).mpr ?_⟩
  intro n' hn'
  obtain ⟨N, hN, rfl⟩ := (he w n').mp hn'
  obtain ⟨p, k, hp, hkw, hkb, hNk, hpk⟩ :=
    generic_meets_decision hZF hU hB hR (hTests.2.2 b hbTests) hN
  obtain ⟨_, _, sk, hsk, hMem⟩ := (hE p k).mp hpk
  have hkT : K.mem (e k) T := (qval_mem_forcing_l O hZF hU (hv k sk hsk) hT).mp ⟨p, hp, hMem⟩
  refine ⟨e k, mem_image hkw, ?_, (hd (e k)).mpr ⟨hkT, mem_image hkb⟩⟩
  rcases hNk with rfl | hNk
  · exact Or.inr rfl
  · exact Or.inl (mem_image hNk)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

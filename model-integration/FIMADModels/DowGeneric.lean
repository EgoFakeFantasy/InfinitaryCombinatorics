import FIMADModels.DowSeparator
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer
import YesMetaZFC.Model.Forcing.Internal.Extension.Choice
import YesMetaZFC.Model.Forcing.Internal.Extension.Generic

/-! A real internal name for the union of generic Dow stems. The generic
filter is an external predicate, whereas the name is an actual ground-model
set constructed by replacement and weighted separation. No external
well-foundedness or standardness of the ground model is assumed. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def InStem (p k : M.Domain) : Prop :=
  ∃ s S, KPair_d M p s S ∧ M.mem k s

namespace Syntax
def inStemFormula {n} (p k : Project.Term n) : Project.Formula 1 n :=
  .existsE (.existsE (.conj (kpair_m p.weaken.weaken (.bound 1) .newest)
    (.mem k.weaken.weaken (.bound 1))))
derive_free_closed inStemFormula

theorem inStemFormula_semantics (hE : Extensional M) {n} (ρ : Env M n)
    (p k : Project.Term n) : Project.Formula.satisfies ρ (inStemFormula p k) ↔
      InStem (p.eval ρ) (k.eval ρ) := by
  simp only [inStemFormula, InStem, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff, kpair_sat_l M hE,
    Project.Formula.satisfies_mem_iff, Definitional.Term.eval_weaken,
    Definitional.Term.eval_newest]
  rfl
end Syntax

theorem check_image_exists (hZF : M.Models SetTheory.ZF) {B c : M.Domain}
    (hc : M.mem c B) (w : M.Domain) :
    ∃ S, (∀ s, M.mem s S ↔ ∃ k, M.mem k w ∧ Check_d M c k s) ∧
      ∀ s, M.mem s S → Name_d M B s := by
  let ρ : Env M 1 := ⟨fun _ => c, fun _ => c⟩
  let φ : BinarySchema 1 := { body := check_m (.bound 2) (.bound 1) .newest }
  have hφ k s : φ.denote ρ k s ↔ Check_d M c k s :=
    check_sat_l M hZF.1 _ _ _ _
  obtain ⟨S, hS⟩ := ZF.exists_functionalImageOn hZF φ ρ w
    (fun k _ => by
      obtain ⟨s, hs, _, _⟩ := zf_check_l M hZF hc k
      exact ⟨s, (hφ k s).mpr hs⟩)
    (fun k _ s t hs ht => check_unique_l M hZF.1 (check_ind_l M hZF)
      c k s t ((hφ k s).mp hs) ((hφ k t).mp ht))
  have he s : M.mem s S ↔ ∃ k, M.mem k w ∧ Check_d M c k s := by
    rw [hS s]
    exact exists_congr fun k => and_congr_right fun _ => hφ k s
  exact ⟨S, he, fun s hs => (he s).mp hs |>.elim fun k hk =>
    check_name_l M (check_range_l M hZF) hc hk.2⟩

/-- The name has exactly the weighted entries check(k), p for k in stem(p). -/
theorem generic_stem_name (hZF : M.Models SetTheory.ZF) {w A B c : M.Domain}
    (hc : M.mem c B) (hB : ∀ p, M.mem p B ↔ CodedCondition w A p) :
    ∃ t, Name_d M B t ∧ ∀ s p, Entry_d M s p t ↔
      M.mem p B ∧ ∃ k, M.mem k w ∧ Check_d M c k s ∧ InStem p k := by
  obtain ⟨S, hS, hNames⟩ := check_image_exists hZF hc w
  let ρ : Env M 1 := ⟨fun _ => c, fun _ => c⟩
  let φ : BinarySchema 1 := {
    body := .existsE (.conj (check_m (.bound 3) .newest (.bound 2))
      (Syntax.inStemFormula (.bound 1) .newest)) }
  have hφ s p : φ.denote ρ s p ↔ ∃ k, Check_d M c k s ∧ InStem p k := by
    simp only [BinarySchema.denote, φ, Project.Formula.satisfies_exists_iff,
      Project.Formula.satisfies_conj_iff, check_sat_l M hZF.1,
      Syntax.inStemFormula_semantics hZF.1]
    rfl
  obtain ⟨t, ht, _, he⟩ := name_comp_l M hZF φ ρ B S hNames
  refine ⟨t, ht, fun s p => (he s p).trans ?_⟩
  rw [hφ s p]
  constructor
  · rintro ⟨_, hp, k, hk, stem, forbidden, hpair, hks⟩
    have hCond := condition_of_codes hZF hpair ((hB p).mp hp)
    exact ⟨hp, k, hCond.1.1 k hks, hk, stem, forbidden, hpair, hks⟩
  · rintro ⟨hp, k, hkw, hk, hStem⟩
    exact ⟨(hS s).mpr ⟨k, hkw, hk⟩, hp, k, hk, hStem⟩

theorem generic_meets_hit (hZF : M.Models SetTheory.ZF) {w A B R a n : M.Domain}
    {U : M.Domain → Prop} (hU : Generic_d M B R B U)
    (hw : M.IsOmega w) (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔
      M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (ha : M.mem a A) (haw : Internal.Subset M.mem a w)
    (hi : Internal.Infinite M.mem w a) (hn : M.mem n w) :
    ∃ p, U p ∧ Hit a n p := by
  let ρ : Env M 2 := (⟨fun _ => a, fun _ => a⟩ : Env M 1).push n
  let φ : UnarySchema 2 := { body := Syntax.hitFormula (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  have hd p : M.mem p D ↔ M.mem p B ∧ Hit a n p := by
    rw [hD p]
    exact and_congr_right fun _ => Syntax.hitFormula_semantics hZF.1 _ _ _ _
  obtain ⟨p, hp⟩ := hU.inhabited
  obtain ⟨q, hq, hqd⟩ := hU.meets p hp D (fun r hr => by
    obtain ⟨s, hs, hsr, hh⟩ := hit_dense hZF hw hB hR ha haw hi hn r hr.1
    have hsz : s ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hs)
    exact ⟨s, ⟨hs, hsz, hsr⟩, (hd s).mpr ⟨hs, hh⟩⟩)
  exact ⟨q, hq, ((hd q).mp hqd).2⟩

theorem generic_meets_avoid (hZF : M.Models SetTheory.ZF) {w A B R b : M.Domain}
    {U : M.Domain → Prop} (hU : Generic_d M B R B U)
    (hw : M.IsOmega w) (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔
      M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hb : Orthogonal w A b) : ∃ p, U p ∧ Avoid w b p := by
  let ρ : Env M 2 := (⟨fun _ => w, fun _ => w⟩ : Env M 1).push b
  let φ : UnarySchema 2 := { body := Syntax.avoidFormula (.bound 2) (.bound 1) .newest }
  obtain ⟨D, hD⟩ := ZF.separation_exists_d hZF φ ρ B
  have hd p : M.mem p D ↔ M.mem p B ∧ Avoid w b p := by
    rw [hD p]
    exact and_congr_right fun _ => Syntax.avoidFormula_semantics hZF.1 _ _ _ _
  obtain ⟨p, hp⟩ := hU.inhabited
  obtain ⟨q, hq, hqd⟩ := hU.meets p hp D (fun r hr => by
    obtain ⟨s, hs, hsr, hh⟩ := avoid_dense hZF hw hB hR hb r hr.1
    have hsz : s ≠ B := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hs)
    exact ⟨s, ⟨hs, hsz, hsr⟩, (hd s).mpr ⟨hs, hh⟩⟩)
  exact ⟨q, hq, ((hd q).mp hqd).2⟩

theorem generic_stem_real (hZF : M.Models SetTheory.ZF) {w A B R c : M.Domain}
    {U : M.Domain → Prop} (O : Cond_order_d M B R B)
    (hU : Generic_d M B R B U) (hc : U c)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a)) :
    ∃ X : (extension_l M hZF B R B U).Domain, ∀ y,
      y ∈ X ↔ ∃ k p, M.mem k w ∧ U p ∧ InStem p k ∧ e k = y := by
  obtain ⟨t, ht, he⟩ := generic_stem_name hZF (hU.proper c hc).1 hB
  obtain ⟨X, hX⟩ := name_value_l (R := R) (z := B) (U := U) ht
  refine ⟨X, fun y => ?_⟩
  rw [qval_mem_l O hZF hU hX]
  constructor
  · rintro ⟨s, p, hs, hp, hsy⟩
    obtain ⟨_, k, hkw, hCheck, hStem⟩ := (he s p).mp hs
    exact ⟨k, p, hkw, hp, hStem, qval_unique_l (hv k s hCheck) hsy⟩
  · rintro ⟨k, p, hkw, hp, hStem, rfl⟩
    obtain ⟨s, hCheck, _, _⟩ := zf_check_l M hZF (hU.proper c hc).1 k
    exact ⟨s, p, (he s p).mpr ⟨(hU.proper p hp).1, k, hkw, hCheck, hStem⟩,
      hp, hv k s hCheck⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

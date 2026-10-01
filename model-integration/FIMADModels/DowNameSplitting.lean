import FIMADModels.DowNameFamilyTheorem

/-! Both sides of splitting for actual forcing-name values. All finiteness
and infinitude predicates belong to the generic quotient's own ZF universe.
-/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def SplitsSet (w X b : M.Domain) : Prop :=
  ∃ d e, Internal.Inter M.mem d X b ∧ Internal.Difference M.mem e X b ∧
    Internal.Infinite M.mem w d ∧ Internal.Infinite M.mem w e

def SplitsTests (w b H : M.Domain) : Prop :=
  ∀ X, M.mem X H → Internal.Infinite M.mem w X → SplitsSet w X b

theorem splitting_meets_tests {w b H : M.Domain} (hSplit : SplitsTests w b H) :
    MeetsTests w b H := by
  intro X hX hi
  obtain ⟨d, _, hd, _, hdi, _⟩ := hSplit X hX hi
  exact ⟨d, hd, hdi⟩

theorem complement_meets_tests {w b H c : M.Domain}
    (hH : ∀ X, M.mem X H → Internal.Subset M.mem X w)
    (hc : Internal.Difference M.mem c w b) (hSplit : SplitsTests w b H) : MeetsTests w c H := by
  intro X hX hi
  obtain ⟨_, e, _, he, _, hei⟩ := hSplit X hX hi
  refine ⟨e, fun k => (he k).trans ?_, hei⟩
  constructor
  · rintro ⟨hkX, hkb⟩
    exact ⟨hkX, (hc k).mpr ⟨hH X hX k hkX, hkb⟩⟩
  · rintro ⟨hkX, hkc⟩
    exact ⟨hkX, ((hc k).mp hkc).2⟩

theorem name_splitting_in_extension (hZF : M.Models SetTheory.ZF)
    {w A B R c L H b t : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U) (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hTests : NameFamilyTests w A B R c L H) (htL : M.mem t L)
    (hb : Internal.Subset M.mem b w) (hSplit : SplitsTests w b H)
    (e : M.Domain → (extension_l M hZF B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a))
    {T : (extension_l M hZF B R B U).Domain} (hT : Qval_d M B R B U t T)
    (hTw : Internal.Subset (extension_l M hZF B R B U).mem T (e w)) :
    SplitsSet (M := extension_l M hZF B R B U) (e w) T (e b) := by
  obtain ⟨E, hE, hGood⟩ := hTests.2.2 t htL
  have hSingle : TallTestsWitness w A E H := ⟨hTests.1, hTests.2.1, hGood⟩
  obtain ⟨d, hd, hdi⟩ := name_intersection_in_extension hZF O hU hw hB hR hE hSingle hb
    (splitting_meets_tests hSplit) e hi he hv hT
  obtain ⟨b', hb'⟩ := KP.difference_exists_d (ZF.modelsKP hZF) b w
  have hb'w : Internal.Subset M.mem b' w := fun k hk => ((hb' k).mp hk).1
  obtain ⟨f, hf, hfi⟩ := name_intersection_in_extension hZF O hU hw hB hR hE hSingle hb'w
    (complement_meets_tests hTests.2.1 hb' hSplit) e hi he hv hT
  refine ⟨d, f, hd, ?_, hdi, hfi⟩
  intro y
  rw [hf y]
  constructor
  · rintro ⟨hyT, hyb'⟩
    obtain ⟨k, hkb', rfl⟩ := (he b' y).mp hyb'
    refine ⟨hyT, ?_⟩
    intro hekb
    obtain ⟨j, hjb, hjk⟩ := (he b (e k)).mp hekb
    exact ((hb' k).mp hkb').2 (hi hjk ▸ hjb)
  · rintro ⟨hyT, hyb⟩
    obtain ⟨k, hkw, rfl⟩ := (he w y).mp (hTw y hyT)
    have hkb : ¬ M.mem k b := fun hk => hyb ((he b (e k)).mpr ⟨k, hk, rfl⟩)
    exact ⟨hyT, (he b' (e k)).mpr ⟨k, (hb' k).mpr ⟨hkw, hkb⟩, rfl⟩⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

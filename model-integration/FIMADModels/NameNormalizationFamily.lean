import FIMADModels.NameNormalization
import YesMetaZFC.SetTheory.CollectionChoice

/-! Countable internally selected families of normalized real names.
Collection and choice produce a model function graph; an actual countable
image supplies the new family, without an external sequence of choices. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem countable_name_normalizations (hZFC : M.Models SetTheory.ZFC)
    {w B R z W L : M.Domain} (O : Cond_order_d M B R z)
    (hW : Name_d M B W) (hL : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t)
    (hOmega : ∀ p, M.mem p B → p ≠ z → Forces_d M B R z
      (Project.Formula.isOmega .newest : Project.Formula 1 1)
      (⟨fun _ => W, fun _ => W⟩ : Env M 1) p) :
    ∃ G C, InternalCountable w C ∧
      (∀ v, M.mem v C ↔ ∃ t, M.mem t L ∧ Entry_d M t v G) ∧
      (∀ t, M.mem t L → ∃ v, M.mem v C ∧ Entry_d M t v G) ∧
      (∀ t v, Entry_d M t v G → NormalizesInfiniteName B R z W t v) := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 4 := (((⟨fun _ => B, fun _ => B⟩ : Env M 1).push R).push z).push W
  let φ : BinarySchema 4 := {
    body := Syntax.normalizesInfiniteNameFormula (.bound 5) (.bound 4) (.bound 3)
      (.bound 2) (.bound 1) .newest }
  have hφ t v : φ.denote ρ t v ↔ NormalizesInfiniteName B R z W t v :=
    Syntax.normalizesInfiniteNameFormula_semantics hZF.1 _ _ _ _ _ _ _
  obtain ⟨Y, G, hG, he⟩ := ZFC.collect_choice_l I hZFC φ ρ L (fun t ht => by
    obtain ⟨v, hv⟩ := infinite_name_normalization hZFC O hW (hNames t ht) hOmega
    exact ⟨v, (hφ t v).mpr hv⟩)
  let η : Env M 1 := ⟨fun _ => G, fun _ => G⟩
  let ψ : BinarySchema 1 := { body := entry_m (.bound 1) .newest (.bound 2) }
  have hψ t v : ψ.denote η t v ↔ Entry_d M t v G := entry_sat_l M hZF.1 _ _ _ _
  obtain ⟨C, hC, hCc⟩ := countable_test_image hZFC ψ η hL (by
    intro t ht
    obtain ⟨v, _, htv⟩ := hG.2.2 t ht
    exact ⟨v, (hψ t v).mpr htv⟩) (by
      intro t _ v v' hv hv'
      exact hG.1.2 t v v' ((hψ t v).mp hv) ((hψ t v').mp hv'))
  have hC' v : M.mem v C ↔ ∃ t, M.mem t L ∧ Entry_d M t v G := by
    rw [hC]
    exact exists_congr fun t => and_congr_right fun _ => hψ t v
  refine ⟨G, C, hCc, hC', ?_, fun t v htv => (hφ t v).mp (he t v htv)⟩
  intro t ht
  obtain ⟨v, _, htv⟩ := hG.2.2 t ht
  exact ⟨v, (hC' v).mpr ⟨t, ht, htv⟩, htv⟩

theorem check_omega_globally_forced (hZF : M.Models SetTheory.ZF)
    {w B R c W : M.Domain} (O : Cond_order_d M B R B)
    (hw : M.IsOmega w) (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) :
    ∀ p, M.mem p B → p ≠ B → Forces_d M B R B
      (Project.Formula.isOmega .newest : Project.Formula 1 1)
      (⟨fun _ => W, fun _ => W⟩ : Env M 1) p := by
  intro p hp hz
  exact check_omega_force_l O hZF hw hc hW ⟨hp, hz, hTop p hp⟩

theorem dow_countable_name_normalizations (hZFC : M.Models SetTheory.ZFC)
    {w B R c W L : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hL : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t) :
    ∃ G C, InternalCountable w C ∧
      (∀ v, M.mem v C ↔ ∃ t, M.mem t L ∧ Entry_d M t v G) ∧
      (∀ t, M.mem t L → ∃ v, M.mem v C ∧ Entry_d M t v G) ∧
      (∀ t v, Entry_d M t v G → NormalizesInfiniteName B R B W t v) := by
  let hZF := ZFC.models_zf_l hZFC
  exact countable_name_normalizations hZFC O (check_name_l M (check_range_l M hZF) hc hW)
    hL hNames (check_omega_globally_forced hZF O hw hc hTop hW)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

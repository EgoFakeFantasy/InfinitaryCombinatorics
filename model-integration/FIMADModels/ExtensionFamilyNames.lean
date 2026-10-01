import FIMADModels.FunctionCanonicalValues

/-! Every internally countable family of infinite reals in an actual generic
quotient is covered by values of one internally countable ground set of names.
The proof uses the quotient's internal omega-function enumeration, the forcing
truth theorem, canonical indices, and the original maximum principle. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem countable_extension_family_names (hZFC : M.Models SetTheory.ZFC)
    {w B R c W : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U) (hw : M.IsOmega w)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W)
    (e : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a))
    {F : (extension_l M (ZFC.models_zf_l hZFC) B R B U).Domain}
    (hF : InternalCountable (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) F)
    (hGood : InfiniteRealFamily (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) F) :
    ∃ L, InternalCountable w L ∧ (∀ t, M.mem t L → Name_d M B t) ∧
      ∀ T, (extension_l M (ZFC.models_zf_l hZFC) B R B U).mem T F →
        ∃ t, M.mem t L ∧ Qval_d M B R B U t T := by
  let hZF := ZFC.models_zf_l hZFC
  let E := extension_l M hZF B R B U
  have hE : E.Models SetTheory.ZF := preserves_zf_l O hZF hU
  have hwE : E.IsOmega (e w) := image_omega_l (hEN := hE.1) e hi he hZF
    (internal_foundation_l O hZF hU) hw
    (fun X => KP.difference_exists_d (ZF.modelsKP hE) X (e w))
  obtain ⟨Q, hEnum⟩ := countable_real_family_enumeration hE hwE hF hGood
  obtain ⟨q, hq, hqV⟩ := value_name_l (M := M) (B := B) (R := R) (z := B) (U := U) Q
  let ρ : Env M 2 := (⟨fun _ => W, fun _ => q⟩ : Env M 1).push q
  let η : Env E 2 := (⟨fun _ => e w, fun _ => Q⟩ : Env E 1).push Q
  have hEnv : Env_val_d hZF ρ η := by
    intro a
    cases a with
    | free _ => exact hqV
    | bound i => exact Fin.cases hqV (fun _ => hv w W hW) i
  obtain ⟨p, hpU, hFunction⟩ := (forcing_truth_l O hZF hU
    (Internal.Syntax.FunctionOnFormula .newest (.bound 1))
    (Internal.Syntax.closed_FunctionOnFormula _ _ rfl rfl) ρ η hEnv).mpr
      ((Internal.Syntax.satisfies_FunctionOnFormula hE.1 η .newest (.bound 1)).mpr hEnum.1)
  obtain ⟨G, L, hLc, hL, hGL, hMax⟩ := countable_function_value_names (w := w) hZFC O hq hc
  refine ⟨L, hLc, ?_, ?_⟩
  · intro t ht
    obtain ⟨n, _, hnt⟩ := (hL t).mp ht
    exact (hMax n t hnt).1
  · intro T hTF
    obtain ⟨n', hn', hn'T⟩ := hEnum.2.2 T hTF
    obtain ⟨n, hn, rfl⟩ := (he w n').mp hn'
    obtain ⟨t, htL, hnt⟩ := hGL n hn
    obtain ⟨ht, s, hs, hValue⟩ := hMax n t hnt
    have hExists := forced_function_value_exists hZF O hc hTop hW hq hn hs
      (hU.proper p hpU).1 (hU.proper p hpU).2 hFunction
    have hForced := hValue p (hU.proper p hpU).1 (hU.proper p hpU).2 hExists
    obtain ⟨V, htV⟩ := name_value_l (R := R) (z := B) (U := U) ht
    let τ : Env M 3 := ((⟨fun _ => q, fun _ => q⟩ : Env M 1).push s).push t
    let ζ : Env E 3 := ((⟨fun _ => Q, fun _ => Q⟩ : Env E 1).push (e n)).push V
    have hValues : Env_val_d hZF τ ζ := by
      intro a
      cases a with
      | free _ => exact hqV
      | bound i => exact Fin.cases htV (Fin.cases (hv n s hs) (fun _ => hqV)) i
    have hActual := (forcing_truth_l O hZF hU Syntax.functionValueSchema.body
      Syntax.functionValueSchema.freeClosed τ ζ hValues).mp ⟨p, hpU, hForced⟩
    have hnV : Internal.Value E.mem Q (e n) V :=
      (Internal.Syntax.satisfies_ValueFormula hE.1 ζ (.bound 2) (.bound 1) .newest).mp hActual
    obtain ⟨Y, _, hUnique⟩ := hEnum.1.2 (e n) hn'
    have hVT : V = T := (hUnique V hnV).trans (hUnique T hn'T).symm
    exact ⟨t, htL, hVT ▸ htV⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

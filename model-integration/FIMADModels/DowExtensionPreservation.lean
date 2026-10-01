import FIMADModels.ExtensionFamilyNames

/-! Actual single-step preservation of omega-splitting in arbitrary internal
Dow generic quotients. All extension countable families are covered by an
internal ground set of names, rather than supplied as an extra premise. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem countable_family_splitting_in_extension (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W S : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U) (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hS : OmegaSplittingTests w S)
    (e : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a))
    {F : (extension_l M (ZFC.models_zf_l hZFC) B R B U).Domain}
    (hF : InternalCountable (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) F)
    (hGood : InfiniteRealFamily (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) F) :
    ∃ b, M.mem b S ∧ Internal.Subset M.mem b w ∧ ∀ T,
      (extension_l M (ZFC.models_zf_l hZFC) B R B U).mem T F →
      SplitsSet (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) T (e b) := by
  let hZF := ZFC.models_zf_l hZFC
  let E := extension_l M hZF B R B U
  have hE : E.Models SetTheory.ZF := preserves_zf_l O hZF hU
  obtain ⟨L, hLc, hNames, hCover⟩ := countable_extension_family_names
    hZFC O hU hw hc hTop hW e hi he hv hF hGood
  obtain ⟨b, bs, hbS, hbw, hbs, hSplit⟩ := preserves_countable_names
    hZFC hw O hB hR hc hTop hW hLc hNames hS
  refine ⟨b, hbS, hbw, fun T hTF => ?_⟩
  obtain ⟨t, htL, htV⟩ := hCover T hTF
  let ρ : Env M 2 := (⟨fun _ => W, fun _ => t⟩ : Env M 1).push t
  let η : Env E 2 := (⟨fun _ => e w, fun _ => T⟩ : Env E 1).push T
  have hVal : Env_val_d hZF ρ η := by
    intro a
    cases a with
    | free _ => exact htV
    | bound i => exact Fin.cases htV (fun _ => hv w W hW) i
  obtain ⟨p, hpU, hInf⟩ := (forcing_truth_l O hZF hU Syntax.infiniteRealSchema.body
    Syntax.infiniteRealSchema.freeClosed ρ η hVal).mpr
      ((Syntax.infiniteRealSchema_semantics hE.1 (⟨fun _ => e w, fun _ => T⟩ : Env E 1) T).mpr
        (hGood T hTF))
  have hForced := hSplit t htL p (hU.proper p hpU).1 hInf
  let τ : Env M 3 := ρ.push bs
  let ζ : Env E 3 := η.push (e b)
  have hValues : Env_val_d hZF τ ζ := by
    intro a
    cases a with
    | free _ => exact htV
    | bound i => exact Fin.cases (hv b bs hbs) (fun i => hVal (.bound i)) i
  exact (Syntax.splitsSetFormula_semantics hE.1 ζ (.bound 2) (.bound 1) .newest).mp
    ((forcing_truth_l O hZF hU (Syntax.splitsSetFormula (.bound 2) (.bound 1) .newest)
      (Syntax.splitsSetFormula_freeClosed _ _ _ rfl rfl rfl) τ ζ hValues).mp ⟨p, hpU, hForced⟩)

theorem omega_splitting_in_extension (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W S : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M B R B) (hU : Generic_d M B R B U) (hw : M.IsOmega w)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hS : OmegaSplittingTests w S)
    (e : M.Domain → (extension_l M (ZFC.models_zf_l hZFC) B R B U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, y ∈ e a ↔ ∃ k, M.mem k a ∧ e k = y)
    (hv : ∀ a s, Check_d M c a s → Qval_d M B R B U s (e a)) :
    OmegaSplittingTests (M := extension_l M (ZFC.models_zf_l hZFC) B R B U) (e w) (e S) := by
  let hZF := ZFC.models_zf_l hZFC
  let E := extension_l M hZF B R B U
  have hE : E.Models SetTheory.ZF := preserves_zf_l O hZF hU
  let I := kpair_interpretation_l E hE.1 (KP.exists_pair (ZF.modelsKP hE))
  intro H hHc hHw
  let ρ : Env E 1 := ⟨fun _ => e w, fun _ => e w⟩
  let φ : UnarySchema 1 := { body := Internal.Syntax.InfiniteFormula (.bound 1) .newest }
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hE φ ρ H
  have hF' T : E.mem T F ↔ E.mem T H ∧ Internal.Infinite E.mem (e w) T :=
    (hF T).trans (and_congr_right fun _ => Internal.Syntax.satisfies_InfiniteFormula hE.1 _ _ _)
  obtain ⟨j, hj⟩ := hHc
  have hJ := (ForcingFinite.injection_correct hE j H (e w)).mp hj
  obtain ⟨g, hg⟩ := ZF.exists_restriction hE I j F
  have hG : E.IsSetInjectionFromTo I g F (e w) :=
    ⟨hg.isSetFunctionFromTo hJ.1 (fun T hTF => ((hF' T).mp hTF).1),
      fun x y z hx hy => hJ.2 x y z ((hg.2 x z).mp hx).2 ((hg.2 y z).mp hy).2⟩
  have hFc : InternalCountable (M := E) (e w) F :=
    ⟨g, (ForcingFinite.injection_correct hE g F (e w)).mpr hG⟩
  have hGood : InfiniteRealFamily (M := E) (e w) F := fun T hTF =>
    ⟨hHw T ((hF' T).mp hTF).1, ((hF' T).mp hTF).2⟩
  obtain ⟨b, hbS, hbw, hSplit⟩ := countable_family_splitting_in_extension
    hZFC O hU hw hB hR hc hTop hW hS e hi he hv hFc hGood
  refine ⟨e b, (he S (e b)).mpr ⟨b, hbS, rfl⟩, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, hn, rfl⟩ := (he b y).mp hy
    exact (he w (e n)).mpr ⟨n, hbw n hn, rfl⟩
  · intro T hTH hTI
    exact hSplit T ((hF' T).mpr ⟨hTH, hTI⟩)

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

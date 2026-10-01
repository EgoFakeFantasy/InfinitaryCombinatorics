import FIMADModels.NameNormalizationFamily

/-! Dow preservation for every internally countable ground set of names.
Each input is required to be an infinite real only at the condition where
splitting is asserted. Actual internal normalization removes the former
global infinitude requirement on each input name. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

def SplitsInfiniteNames (B R W L bs : M.Domain) : Prop :=
  ∀ t, M.mem t L → ∀ p, M.mem p B → ForcesInfiniteReal B R B W t p →
    Forces_d M B R B (Syntax.splitsSetFormula (.bound 2) (.bound 1) .newest)
      (((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t).push bs) p

theorem preserves_countable_names (hZFC : M.Models SetTheory.ZFC)
    {w A B R c W L S : M.Domain} (hw : M.IsOmega w) (O : Cond_order_d M B R B)
    (hB : ∀ p, M.mem p B ↔ CodedCondition w A p)
    (hR : ∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ CodedExtends (M := M) p q)
    (hc : M.mem c B) (hTop : ∀ p, M.mem p B → Entry_d M p c R)
    (hW : Check_d M c w W) (hLc : InternalCountable w L)
    (hNames : ∀ t, M.mem t L → Name_d M B t)
    (hS : OmegaSplittingTests w S) :
    ∃ b bs, M.mem b S ∧ Internal.Subset M.mem b w ∧ Check_d M c b bs ∧
      SplitsInfiniteNames B R W L bs := by
  let hZF := ZFC.models_zf_l hZFC
  have hWN := check_name_l M (check_range_l M hZF) hc hW
  have positive {p} (hp : M.mem p B) : p ≠ B :=
    fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) B (eq ▸ hp)
  obtain ⟨G, C, hCc, hC, hGC, hNorm⟩ :=
    dow_countable_name_normalizations hZFC hw O hc hTop hW hLc hNames
  have norm_names v (hvC : M.mem v C) : Name_d M B v ∧ ForcesUnboundedName B R W v := by
    obtain ⟨t, _, htv⟩ := (hC v).mp hvC
    have hn := hNorm t v htv
    have hg p (hp : M.mem p B) := (hn.2 p hp (positive hp)).1
    have hcj p (hp : M.mem p B) := (forces_conj_l _ _ _ p).mp (hg p hp)
    exact ⟨hn.1, globally_forced_infinite_unbounded hZF O hw hc hTop hW hn.1
      (fun p hp => (forces_subset_original_iff _).mp (hcj p hp).1)
      (fun p hp => (hcj p hp).2)⟩
  obtain ⟨b, bs, hbS, hbw, hbs, hSplit⟩ := preserves_countable_unbounded_names
    hZFC hw O hB hR hc hTop hW hCc norm_names hS
  have hbsN := check_name_l M (check_range_l M hZF) hc hbs
  refine ⟨b, bs, hbS, hbw, hbs, fun t htL p hp hInf => ?_⟩
  obtain ⟨v, hvC, htv⟩ := hGC t htL
  have hn := hNorm t v htv
  have hg := (forces_conj_l _ _ _ p).mp (hn.2 p hp (positive hp)).1
  have hSub : Forces_d M B R B (Project.Formula.subset (.bound 1) .newest : Project.Formula 1 2)
      ((⟨fun _ => v, fun _ => v⟩ : Env M 1).push W) p := by
    have hs0 : Forces_d M B R B (Project.Formula.subset .newest (.bound 1) : Project.Formula 1 2)
        ((⟨fun _ => W, fun _ => v⟩ : Env M 1).push v) p :=
      (forces_subset_original_iff ((⟨fun _ => W, fun _ => v⟩ : Env M 1).push v)).mp hg.1
    have hb : (Project.Formula.subset .newest (.bound 1) : Project.Formula 1 2).bind
        (Fin.cases (.bound 1) (fun _ => (.newest : Project.Term 2))) =
        Project.Formula.subset (.bound 1) (.newest : Project.Term 2) := by
      simp [Project.Formula.subset, Project.Formula.pairArguments, Definitional.Formula.bind,
        Definitional.Term.bind, Definitional.TermVector.bind, Definitional.Term.newest,
        Fin.cases, Fin.induction, Fin.induction.go]
    rw [← hb, forces_bind_l hZF.1]
    have he : Definitional.Env.substitute ((⟨fun _ => v, fun _ => v⟩ : Env M 1).push W)
        (Fin.cases (.bound 1) (fun _ => (.newest : Project.Term 2))) =
        ((⟨fun _ => W, fun _ => v⟩ : Env M 1).push v) := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
    rw [he]
    exact hs0
  have hs := hSplit v hvC p hp hSub
  let ρ : Env M 3 := ((⟨fun _ => W, fun _ => W⟩ : Env M 1).push v).push bs
  let η : Env M 3 := ((⟨fun _ => W, fun _ => W⟩ : Env M 1).push t).push bs
  have hρ : ∀ a : Project.Term 3, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hWN
    | bound i => exact Fin.cases hbsN (Fin.cases hn.1 (fun _ => hWN)) i
  have hη : ∀ a : Project.Term 3, Name_d M B (a.eval η) := by
    intro a
    cases a with
    | free _ => exact hWN
    | bound i => exact Fin.cases hbsN (Fin.cases (hNames t htL) (fun _ => hWN)) i
  have he : ∀ a : Project.Term 3, Eq_force_d M B R B p (a.eval ρ) (a.eval η) := by
    intro a
    cases a with
    | free _ => exact eq_force_refl_l O hZF hp hWN
    | bound i =>
      exact Fin.cases (eq_force_refl_l O hZF hp hbsN)
        (Fin.cases ((hn.2 p hp (positive hp)).2 hInf) (fun _ => eq_force_refl_l O hZF hp hWN)) i
  have hs' := (forces_env_l hZF.1 _ (Syntax.splitsSetFormula_freeClosed _ _ _ rfl rfl rfl)
    (((⟨fun _ => W, fun _ => v⟩ : Env M 1).push v).push bs) ρ
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp hs
  have ht' := (forces_congr_below_l O hZF _ ρ η hρ hη hp he p
    (below_refl_l O hp (positive hp))).mp hs'
  exact (forces_env_l hZF.1 _ (Syntax.splitsSetFormula_freeClosed _ _ _ rfl rfl rfl) η
    (((⟨fun _ => W, fun _ => t⟩ : Env M 1).push t).push bs)
    (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) p).mp ht'

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

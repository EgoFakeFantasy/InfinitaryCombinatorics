import FIMADModels.FunctionValueNames

/-! Total function names have maximum-principle values at every canonical
internal natural-number name, at the original condition of totality. -/

set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal
open YesMetaZFC YesMetaZFC.SetTheory Definitional Definitional.Project
open YesMetaZFC.Model.Forcing.Internal
universe u
variable {M : SetTheory.Structure.{u}}

theorem forced_function_value_exists (hZF : M.Models SetTheory.ZF)
    {w B R c W Q n s p : M.Domain} (O : Cond_order_d M B R B)
    (hc : M.mem c B) (hTop : ∀ q, M.mem q B → Entry_d M q c R)
    (hW : Check_d M c w W) (hQ : Name_d M B Q) (hn : M.mem n w)
    (hs : Check_d M c n s) (hp : M.mem p B) (hz : p ≠ B)
    (hFunction : Forces_d M B R B (Internal.Syntax.FunctionOnFormula .newest (.bound 1))
      ((⟨fun _ => W, fun _ => Q⟩ : Env M 1).push Q) p) :
    Forces_d M B R B Syntax.functionValueExistsSchema.body
      ((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push s) p := by
  have hWN := check_name_l M (check_range_l M hZF) hc hW
  have hsN := check_name_l M (check_range_l M hZF) hc hs
  let ρ : Env M 2 := (⟨fun _ => W, fun _ => Q⟩ : Env M 1).push Q
  have hρ : ∀ a : Project.Term 2, Name_d M B (a.eval ρ) := by
    intro a
    cases a with
    | free _ => exact hQ
    | bound i => exact Fin.cases hQ (fun _ => hWN) i
  have hξ : ∀ a : Project.Term 3, Name_d M B (a.eval (ρ.push s)) := by
    intro a
    cases a with
    | free _ => exact hQ
    | bound i => exact Fin.cases hsN (fun i => hρ (.bound i)) i
  have hValid := forces_zf_valid_l O hZF Syntax.functionTotalBody Syntax.functionTotalBody_closed
    (fun _ hN η => Syntax.functionTotalBody_valid hN η) ρ (fun i => hρ (.bound i)) hp hz
  have hAll := forces_mp_l hZF.1 (forces_regular_l O hZF _ ρ hρ).1
    (forces_regular_l O hZF _ ρ hρ) hp hz hValid hFunction
  have hAt := (forces_all_l hZF.1 _ ρ p).mp hAll s hsN
  have hMem : Forces_d M B R B (.mem .newest (.bound 2) : Project.Formula 1 3) (ρ.push s) p :=
    (forces_mem_l hZF.1 _ _ _ _).mpr (check_mem_force_l O hZF hc hs hW hp (hTop p hp) hn)
  have hExists := forces_mp_l hZF.1 (forces_regular_l O hZF _ (ρ.push s) hξ).1
    (forces_regular_l O hZF _ (ρ.push s) hξ) hp hz hAt hMem
  have h := (forces_pred_l hZF.1 Syntax.functionValueExistsSchema (ρ.push s)
    (fun _ => (.bound 1 : Project.Term 3)) .newest p).mp hExists
  exact (forces_env_l hZF.1 Syntax.functionValueExistsSchema.body
    Syntax.functionValueExistsSchema.freeClosed
    ((⟨fun _ => (.bound 1 : Project.Term 3).eval (ρ.push s), (ρ.push s).free⟩ : Env M 1).push
      ((.newest : Project.Term 3).eval (ρ.push s)))
    ((⟨fun _ => Q, fun _ => Q⟩ : Env M 1).push s)
    (Fin.cases rfl (fun _ => rfl)) p).mp h

end InfinitaryCombinatorics.Formalizations.FIMAD.DowInternal

import Formalizations.FIMAD.CheckedZFC
import YesMetaZFC.Model.Boolean.Schemas
import YesMetaZFC.Model.Boolean.Choice
import YesMetaZFC.Model.Boolean.Infinity

/-! Standard Boolean names satisfy the kernel-checked ZFC presentation.
Adapted from YesMetaZFC/Model/Boolean/ZFC.lean at 51c348a (Apache-2.0).
Only the fixed sentences' closure certificates are replaced; full separation
and collection and every Boolean name construction are reused unchanged.
See THIRD_PARTY_NOTICES.md for attribution.
-/

namespace InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels
open YesMetaZFC YesMetaZFC.SetTheory YesMetaZFC.SetTheory.Definitional
open YesMetaZFC.Model YesMetaZFC.Model.Boolean BV_graph BV_project

abbrev zfcTheory := Project.fo_theory CheckedZFC.Axiom

namespace CheckedBooleanZFC
universe u
variable {B : Type u} (𝔹 : CB_alg B)
local notation "N" => BV_name B
attribute [local implicit_reducible] name_structure Project.FirstOrderSemantics.reduct SetTheory.signature

theorem project_zfc (s : Project.Sentence) (hs : CheckedZFC.Axiom s) (ρ : BV_project.Env 𝔹 0) :
  𝔹.le 𝔹.top (BV_project.value 𝔹 s.formula ρ) := by
  cases hs with
  | separation φ => exact closure_valid 𝔹 _ ρ (fun b => separation_core 𝔹 φ ⟨b, ρ.free⟩)
  | collection φ => exact closure_valid 𝔹 _ ρ (fun b => collection_core 𝔹 φ ⟨b, ρ.free⟩)
  | extensionality =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.iInf (fun H : N =>
      𝔹.imp (𝔹.iInf (fun K : N => 𝔹.iff (bv_mem 𝔹 K G) (bv_mem 𝔹 K H))) (bv_eq 𝔹 G H))))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    apply (𝔹.le_iInf_iff _ _).mpr
    intro H
    rw [𝔹.valid_imp_iff]
    apply le_eq_of_mem 𝔹 G H
    · intro K
      exact (𝔹.le_imp_iff _ _ _).mp (((𝔹.le_meet_iff _ _ _).mp
        (𝔹.iInf_le (fun K : N => 𝔹.iff (bv_mem 𝔹 K G) (bv_mem 𝔹 K H)) K)).1)
    · intro K
      exact (𝔹.le_imp_iff _ _ _).mp (((𝔹.le_meet_iff _ _ _).mp
        (𝔹.iInf_le (fun K : N => 𝔹.iff (bv_mem 𝔹 K G) (bv_mem 𝔹 K H)) K)).2)
  | emptySet =>
    change 𝔹.le 𝔹.top (𝔹.iSup (fun G : N => 𝔹.iInf (fun H : N => 𝔹.neg (bv_mem 𝔹 H G))))
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun G : N => 𝔹.iInf (fun H : N => 𝔹.neg (bv_mem 𝔹 H G)))
      (BV_graph.empty 𝔹.toPO_bot))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro H; rw [empty_mem]; exact 𝔹.le_refl _
  | pairing =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.iInf (fun H : N => 𝔹.iSup (fun C : N =>
      𝔹.iInf (fun K : N => 𝔹.iff (bv_mem 𝔹 K C) (𝔹.join (bv_eq 𝔹 K G) (bv_eq 𝔹 K H)))))))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    apply (𝔹.le_iInf_iff _ _).mpr
    intro H
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun C : N => 𝔹.iInf (fun K : N =>
      𝔹.iff (bv_mem 𝔹 K C) (𝔹.join (bv_eq 𝔹 K G) (bv_eq 𝔹 K H)))) (pair 𝔹 G H))
    exact (𝔹.le_iInf_iff _ _).mpr (fun K => (𝔹.valid_iff_iff _ _).mpr (pair_mem 𝔹 G H K))
  | union =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.iSup (fun C : N => 𝔹.iInf (fun K : N =>
      𝔹.iff (bv_mem 𝔹 K C) (𝔹.iSup (fun H : N => 𝔹.meet (bv_mem 𝔹 H G) (bv_mem 𝔹 K H)))))))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun C : N => 𝔹.iInf (fun K : N =>
      𝔹.iff (bv_mem 𝔹 K C) (𝔹.iSup (fun H : N => 𝔹.meet (bv_mem 𝔹 H G) (bv_mem 𝔹 K H))))) (union 𝔹 G))
    exact (𝔹.le_iInf_iff _ _).mpr (fun K => (𝔹.valid_iff_iff _ _).mpr (union_mem 𝔹 G K))
  | powerSet =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.iSup (fun C : N =>
      𝔹.iInf (fun H : N => 𝔹.iff (bv_mem 𝔹 H C) (subset 𝔹 H G)))))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun C : N =>
      𝔹.iInf (fun H : N => 𝔹.iff (bv_mem 𝔹 H C) (subset 𝔹 H G))) (power 𝔹 G))
    exact (𝔹.le_iInf_iff _ _).mpr (fun H => (𝔹.valid_iff_iff _ _).mpr (power_mem 𝔹 G H))
  | foundation =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.imp (nonempty_value 𝔹 G)
      (𝔹.iSup (fun H : N => 𝔹.meet (bv_mem 𝔹 H G) (minimal 𝔹 G H)))))
    exact (𝔹.le_iInf_iff _ _).mpr (fun G => (𝔹.valid_imp_iff _ _).mpr (BV_graph.foundation 𝔹 G))
  | infinity =>
    let P (O : N) := 𝔹.meet
      (𝔹.iSup (fun E : N => 𝔹.meet (𝔹.iInf (fun H : N => 𝔹.neg (bv_mem 𝔹 H E))) (bv_mem 𝔹 E O)))
      (𝔹.iInf (fun G : N => 𝔹.imp (bv_mem 𝔹 G O)
        (𝔹.iSup (fun S : N => 𝔹.meet (successor_value 𝔹 G S) (bv_mem 𝔹 S O)))))
    change 𝔹.le 𝔹.top (𝔹.iSup P)
    apply 𝔹.le_trans _ (𝔹.le_iSup P (BV_graph.omega 𝔹))
    obtain ⟨⟨E, he, ho⟩, hs⟩ := BV_graph.infinity 𝔹
    apply 𝔹.le_meet _ hs
    apply 𝔹.le_trans _ (𝔹.le_iSup (fun E : N => 𝔹.meet
      (𝔹.iInf (fun H : N => 𝔹.neg (bv_mem 𝔹 H E))) (bv_mem 𝔹 E (BV_graph.omega 𝔹))) E)
    rw [ho]
    apply 𝔹.le_meet _ (𝔹.le_refl _)
    apply (𝔹.le_iInf_iff _ _).mpr
    intro H; rw [he H]; exact 𝔹.le_refl _
  | choice =>
    change 𝔹.le 𝔹.top (𝔹.iInf (fun G : N => 𝔹.imp
      (𝔹.meet (𝔹.iInf (fun H : N => 𝔹.imp (bv_mem 𝔹 H G) (nonempty_value 𝔹 H))) (pairwise_disjoint 𝔹 G))
      (𝔹.iSup (fun C : N => 𝔹.iInf (fun H : N => 𝔹.imp (bv_mem 𝔹 H G) (selects 𝔹 C H))))))
    apply (𝔹.le_iInf_iff _ _).mpr
    intro G
    rw [𝔹.valid_imp_iff]
    obtain ⟨C, hc⟩ := BV_graph.choice 𝔹 G _ (𝔹.meet_le_left _ _) (𝔹.meet_le_right _ _)
    exact 𝔹.le_trans hc (𝔹.le_iSup (fun C : N =>
      𝔹.iInf (fun H : N => 𝔹.imp (bv_mem 𝔹 H G) (selects 𝔹 C H))) C)


theorem models_zfc : (name_model 𝔹).models zfcTheory := by
  intro φ ⟨s, hs, he⟩ ρ
  subst φ
  change 𝔹.le 𝔹.top (BV_str.value 𝔹 (name_structure 𝔹)
    (Project.fo_formula s.formula s.freeClosed) ρ)
  rw [BV_project.formula_correct 𝔹 s.formula s.freeClosed ρ
    (fun _ => BV_graph.empty 𝔹.toPO_bot)]
  exact project_zfc 𝔹 s hs _

end CheckedBooleanZFC
end InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels

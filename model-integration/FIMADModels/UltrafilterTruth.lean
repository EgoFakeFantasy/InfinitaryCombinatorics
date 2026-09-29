import YesMetaZFC.Model.Boolean.Ultrafilter
import YesMetaZFC.Model.Boolean.Maximum

/-! Truth operations for a maximal proper Boolean filter. Infinite joins require
an attained maximum; no countable completeness or genericity is assumed. -/
namespace InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels
open YesMetaZFC.Model.Boolean
universe u v
variable {B : Type u} (𝔹 : CB_alg B) (U : Filter_l 𝔹.toBA_alg)

namespace UltrafilterTruth

theorem meet_iff (a b : B) : U.mem (𝔹.meet a b) ↔ U.mem a ∧ U.mem b :=
  ⟨fun h => ⟨U.upward h (𝔹.meet_le_left _ _), U.upward h (𝔹.meet_le_right _ _)⟩,
    fun h => U.meet_mem h.1 h.2⟩

theorem neg_iff (hU : U.Maximal_l) (a : B) : U.mem (𝔹.neg a) ↔ ¬ U.mem a := by
  constructor
  · intro h k; exact U.not_neg_l hU.1 k h
  · intro h
    exact ((U.maximal_iff_l.mp hU).2 a).resolve_left h

theorem imp_iff (hU : U.Maximal_l) (a b : B) :
    U.mem (𝔹.imp a b) ↔ (U.mem a → U.mem b) := by
  constructor
  · intro h k
    exact U.upward (U.meet_mem h k) (𝔹.imp_elim _ _)
  · intro h
    by_cases ha : U.mem a
    · exact U.upward (h ha) ((𝔹.le_imp_iff _ _ _).mpr (𝔹.meet_le_left _ _))
    · apply U.upward ((neg_iff 𝔹 U hU a).mpr ha)
      apply (𝔹.le_imp_iff _ _ _).mpr
      exact 𝔹.le_trans (𝔹.imp_elim _ _) (𝔹.bot_le _)

theorem join_iff (hU : U.Maximal_l) (a b : B) :
    U.mem (𝔹.join a b) ↔ U.mem a ∨ U.mem b := by
  classical
  rw [BA_alg.join, neg_iff 𝔹 U hU, meet_iff, neg_iff 𝔹 U hU, neg_iff 𝔹 U hU]
  constructor
  · intro h
    by_cases ha : U.mem a
    · exact Or.inl ha
    · exact Or.inr (Classical.byContradiction (fun hb => h ⟨ha, hb⟩))
  · rintro (ha | hb) ⟨hna, hnb⟩
    · exact hna ha
    · exact hnb hb

theorem iff_iff (hU : U.Maximal_l) (a b : B) :
    U.mem (𝔹.iff a b) ↔ (U.mem a ↔ U.mem b) := by
  rw [BA_alg.iff, meet_iff, imp_iff 𝔹 U hU, imp_iff 𝔹 U hU]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem attained_sup_iff {I : Type v} (p : I → B) (h : ∃ i, p i = 𝔹.iSup p) :
    U.mem (𝔹.iSup p) ↔ ∃ i, U.mem (p i) := by
  constructor
  · intro hp; obtain ⟨i, hi⟩ := h; exact ⟨i, hi ▸ hp⟩
  · rintro ⟨i, hi⟩; exact U.upward hi (𝔹.le_iSup p i)

theorem attained_inf_iff {I : Type v} (p : I → B)
    (h : ∃ i, 𝔹.neg (p i) = 𝔹.iSup (fun j => 𝔹.neg (p j))) :
    U.mem (𝔹.iInf p) ↔ ∀ i, U.mem (p i) := by
  constructor
  · intro hp i; exact U.upward hp (𝔹.iInf_le p i)
  · intro hp
    obtain ⟨i, hi⟩ := h
    apply U.upward (hp i)
    apply (𝔹.le_iInf_iff _ _).mpr
    intro j
    apply (𝔹.neg_le_neg_iff (p j) (p i)).mp
    rw [hi]
    exact 𝔹.le_iSup (fun j => 𝔹.neg (p j)) j

end UltrafilterTruth
end InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels

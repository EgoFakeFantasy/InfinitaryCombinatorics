import Formalizations.R0.Main
import Mathlib.Order.Zorn

/-! Local AD families, maximal extensions, and orthogonal replacement.
Finite local maximal families are allowed; the shared MAD convention is unchanged. -/
namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

def Orthogonal (F : Set (Set X)) : Set (Set X) :=
  {Y | ∀ a ∈ F, (Y ∩ a).Finite}

def MaximalOn (F : Set (Set X)) (U : Set X) : Prop :=
  ADFamily F ∧ (∀ a ∈ F, a ⊆ U) ∧
    ∀ Y ⊆ U, Y.Infinite → ∃ a ∈ F, (Y ∩ a).Infinite

lemma maximalOn_univ_iff {F : Set (Set X)} :
    MaximalOn F univ ↔ ADFamily F ∧
      ∀ Y : Set X, Y.Infinite → ∃ a ∈ F, (Y ∩ a).Infinite := by
  constructor
  · intro h; exact ⟨h.1, fun Y hY => h.2.2 Y (subset_univ _) hY⟩
  · rintro ⟨hF, hm⟩; exact ⟨hF, fun _ _ => subset_univ _, fun Y _ => hm Y⟩

lemma mad_iff_infinite_maximalOn {F : Set (Set X)} :
    MAD F ↔ F.Infinite ∧ MaximalOn F univ := by
  rw [maximalOn_univ_iff]
  simp only [MAD, _root_.R0.AlmostDisjoint, ADFamily, and_assoc]

lemma ad_insert_orthogonal {F : Set (Set X)} (hF : ADFamily F)
    {Y : Set X} (hY : Y.Infinite) (ho : Y ∈ Orthogonal F) :
    ADFamily (insert Y F) := by
  constructor
  · intro a ha
    rcases mem_insert_iff.mp ha with rfl | ha
    · exact hY
    · exact hF.1 a ha
  · intro a ha b hb hab
    by_cases hax : a = Y
    · subst a
      exact ho b ((mem_insert_iff.mp hb).resolve_left (Ne.symm hab))
    · have haF : a ∈ F := (mem_insert_iff.mp ha).resolve_left hax
      by_cases hbx : b = Y
      · subst b
        simpa [inter_comm] using ho a haF
      · exact hF.2 a haF b ((mem_insert_iff.mp hb).resolve_left hbx) hab

/-- Zorn's lemma supplies an actual completion, with no maximality assumption. -/
theorem exists_maximal_extension {F : Set (Set X)} (hF : ADFamily F) :
    ∃ M, F ⊆ M ∧ MaximalOn M univ := by
  classical
  have hub : ∀ c ⊆ {B : Set (Set X) | ADFamily B},
      IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ B ∈ {B : Set (Set X) | ADFamily B}, ∀ D ∈ c, D ⊆ B := by
    intro c hc hchain _
    refine ⟨⋃₀ c, ?_, fun B hB => subset_sUnion_of_mem hB⟩
    constructor
    · rintro a ⟨B, hB, ha⟩
      exact (hc hB).1 a ha
    · rintro a ⟨B, hB, ha⟩ b ⟨D, hD, hb⟩ hab
      by_cases hBD : B = D
      · subst D; exact (hc hB).2 a ha b hb hab
      · rcases hchain hB hD hBD with h | h
        · exact (hc hD).2 a (h ha) b hb hab
        · exact (hc hB).2 a ha b (h hb) hab
  obtain ⟨M, hFM, hm⟩ := zorn_subset_nonempty _ hub F hF
  refine ⟨M, hFM, maximalOn_univ_iff.mpr ⟨hm.1, ?_⟩⟩
  intro Y hY
  by_contra hn
  have ho : Y ∈ Orthogonal M := by
    intro a ha
    exact not_infinite.mp (fun h => hn ⟨a, ha, h⟩)
  have hYM : Y ∈ M := hm.2 (ad_insert_orthogonal hm.1 hY ho)
    (subset_insert _ _) (by simp)
  exact hY (by simpa using ho Y hYM)

lemma exists_mad_extension {F : Set (Set X)} (hF : _root_.R0.AlmostDisjoint F) :
    ∃ M, F ⊆ M ∧ MAD M := by
  obtain ⟨M, hFM, hm⟩ := exists_maximal_extension hF.2
  exact ⟨M, hFM, mad_iff_infinite_maximalOn.mpr ⟨hF.1.mono hFM, hm⟩⟩

def refinement (F : Set (Set X)) (P : Set X → Set (Set X)) : Set (Set X) :=
  ⋃ a ∈ F, P a

lemma mem_refinement {F : Set (Set X)} {P : Set X → Set (Set X)} {p : Set X} :
    p ∈ refinement F P ↔ ∃ a ∈ F, p ∈ P a := by simp only [refinement, mem_iUnion, exists_prop]

lemma refinement_ad {F : Set (Set X)} (hF : ADFamily F)
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a) :
    ADFamily (refinement F P) := by
  constructor
  · intro p hp
    obtain ⟨a, ha, hp⟩ := mem_refinement.mp hp
    exact (hP a ha).1.1 p hp
  · intro p hp q hq hpq
    obtain ⟨a, ha, hp⟩ := mem_refinement.mp hp
    obtain ⟨b, hb, hq⟩ := mem_refinement.mp hq
    by_cases hab : a = b
    · subst b; exact (hP a ha).1.2 p hp q hq hpq
    · exact (hF.2 a ha b hb hab).subset
        (inter_subset_inter ((hP a ha).2.1 p hp) ((hP b hb).2.1 q hq))

/-- Paper Theorem 4.1: equality includes finite orthogonal sets. -/
theorem refinement_orthogonal {F : Set (Set X)}
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a) :
    Orthogonal (refinement F P) = Orthogonal F := by
  ext Y
  constructor
  · intro h a ha
    by_contra hn
    have hi : (Y ∩ a).Infinite := not_finite.mp hn
    obtain ⟨p, hp, hip⟩ := (hP a ha).2.2 (Y ∩ a) inter_subset_right hi
    exact hip ((h p (mem_refinement.mpr ⟨a, ha, hp⟩)).subset
      (fun _ hx => ⟨hx.1.1, hx.2⟩))
  · intro h p hp
    obtain ⟨a, ha, hp⟩ := mem_refinement.mp hp
    exact (h a ha).subset (inter_subset_inter_right _ ((hP a ha).2.1 p hp))

lemma maximalOn_iff_orthogonal {F : Set (Set X)} (hF : ADFamily F) :
    MaximalOn F univ ↔ ∀ Y ∈ Orthogonal F, Y.Finite := by
  rw [maximalOn_univ_iff]
  constructor
  · rintro ⟨_, hm⟩ Y ho
    by_contra hn
    obtain ⟨a, ha, hi⟩ := hm Y (not_finite.mp hn)
    exact hi (ho a ha)
  · intro ho
    refine ⟨hF, ?_⟩
    intro Y hY
    by_contra hn
    exact hY (ho Y (fun a ha => not_infinite.mp (fun h => hn ⟨a, ha, h⟩)))

lemma refinement_maximal {F : Set (Set X)} (hm : MaximalOn F univ)
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a) :
    MaximalOn (refinement F P) univ := by
  apply (maximalOn_iff_orthogonal (refinement_ad hm.1 hP)).mpr
  rw [refinement_orthogonal hP]
  exact (maximalOn_iff_orthogonal hm.1).mp hm

/-- Finite refinements may omit a finite part of their parent. -/
theorem finite_cover_maximalOn {P : Set (Set X)} {a : Set X}
    (hP : ADFamily P) (hf : P.Finite) (hsub : ∀ p ∈ P, p ⊆ a)
    (hcover : (a \ ⋃₀ P).Finite) : MaximalOn P a := by
  refine ⟨hP, hsub, ?_⟩
  intro Y hYa hY
  by_contra hn
  have hsmall : (⋃ p ∈ P, Y ∩ p).Finite := hf.biUnion
    (fun p hp => not_infinite.mp (fun h => hn ⟨p, hp, h⟩))
  apply hY
  apply (hcover.union hsmall).subset
  intro y hy
  by_cases hu : y ∈ ⋃₀ P
  · obtain ⟨p, hp, hyp⟩ := hu
    exact Or.inr (mem_iUnion₂.mpr ⟨p, hp, hy, hyp⟩)
  · exact Or.inl ⟨hYa hy, hu⟩

lemma refinement_card_ge {F : Set (Set X)} (hF : ADFamily F)
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a) :
    #F ≤ #(refinement F P) := by
  classical
  have hex (a : F) : ∃ p ∈ P a, (a.val ∩ p).Infinite :=
    (hP a a.property).2.2 a Subset.rfl (hF.1 a a.property)
  choose p hp hi using hex
  let f : F → refinement F P := fun a => ⟨p a, mem_refinement.mpr ⟨a, a.property, hp a⟩⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro a b h
  apply Subtype.ext
  by_contra hab
  have hpq : p a = p b := congrArg Subtype.val h
  have hfin := hF.2 a a.property b b.property hab
  exact (hP a a.property).1.1 (p a) (hp a) (hfin.subset (fun x hx =>
    ⟨(hP a a.property).2.1 (p a) (hp a) hx,
     (hP b b.property).2.1 (p b) (hp b) (hpq ▸ hx)⟩))

/-- Paper Corollary 4.2, including the exact cardinality. -/
theorem finite_refinement_card {F : Set (Set X)} (hF : _root_.R0.AlmostDisjoint F)
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a)
    (hf : ∀ a ∈ F, (P a).Finite) : #(refinement F P) = #F := by
  have hω : ℵ₀ ≤ #F := Cardinal.aleph0_le_mk_iff.mpr hF.1.to_subtype
  apply le_antisymm ?_ (refinement_card_ge hF.2 hP)
  calc
    #(refinement F P) ≤ #F * ⨆ a : F, #(P a.val) := Cardinal.mk_biUnion_le P F
    _ ≤ #F * ℵ₀ := mul_le_mul_right (ciSup_le' (fun (a : F) =>
      Cardinal.le_aleph0_iff_set_countable.mpr (hf a a.property).countable)) _
    _ = #F := Cardinal.mul_aleph0_eq hω

lemma refinement_mad {F : Set (Set X)} (hF : MAD F)
    {P : Set X → Set (Set X)} (hP : ∀ a ∈ F, MaximalOn (P a) a) :
    MAD (refinement F P) := by
  apply mad_iff_infinite_maximalOn.mpr
  refine ⟨?_, refinement_maximal (mad_iff_infinite_maximalOn.mp hF).2 hP⟩
  exact Set.infinite_coe_iff.mp (Cardinal.aleph0_le_mk_iff.mp
    ((Cardinal.aleph0_le_mk_iff.mpr hF.1.1.to_subtype).trans (refinement_card_ge hF.1.2 hP)))

end InfinitaryCombinatorics.Formalizations.R0

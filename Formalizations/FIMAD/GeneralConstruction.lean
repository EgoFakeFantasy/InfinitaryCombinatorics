import Formalizations.FIMAD.SmallPositiveExtension
import Formalizations.FIMAD.CHConstruction

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal
open InfinitaryCombinatorics.Formalizations.R0 (blocksOver)
open CHConstruction

namespace GeneralConstruction
variable {ι : Type} [LinearOrder ι]

lemma requirements_card_le (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    (B : Set (Set ℕ)) (x : ι) (p : Set.Iio x → FIStage) (I : Set ℕ)
    (hA : (oldFamily B x p).Infinite) :
    #(requirements C X B x p I) ≤ #(Set.Iic x) * #(oldFamily B x p) + 1 := by
  classical
  let A := oldFamily B x p
  letI := hA.to_subtype
  let code (q : Set.Iic x × Finset A) : Set ℕ :=
    blocksOver (C q.1) (tracePattern (C q.1)
      (registeredWitness x p I q.1) (Subtype.val '' (q.2 : Set A)))
  have hs : requirements C X B x p I ⊆ insert (X x) (range code) := by
    rintro Y (hY | hY)
    · exact Or.inl hY
    · obtain ⟨γ, hγ, hY⟩ := mem_iUnion₂.mp hY
      obtain ⟨F, ⟨hF, hFA⟩, hY⟩ := mem_iUnion₂.mp hY
      obtain rfl := mem_singleton_iff.mp hY
      have hP : (Subtype.val ⁻¹' F : Set A).Finite := hF.preimage Subtype.val_injective.injOn
      have he : Subtype.val '' (hP.toFinset : Set A) = F := by
        ext a
        constructor
        · rintro ⟨b, hb, rfl⟩
          exact hP.mem_toFinset.mp hb
        · intro ha
          exact ⟨⟨a, hFA ha⟩, hP.mem_toFinset.mpr ha, rfl⟩
      refine Or.inr ⟨(⟨γ, hγ⟩, hP.toFinset), ?_⟩
      simp only [code, he]
  calc
    #(requirements C X B x p I) ≤ #(insert (X x) (range code) : Set (Set ℕ)) := mk_le_mk_of_subset hs
    _ ≤ #(range code) + 1 := mk_insert_le
    _ ≤ #(Set.Iic x × Finset A) + 1 := by
      exact add_le_add mk_range_le le_rfl
    _ = #(Set.Iic x) * #A + 1 := by simp only [mk_prod, mk_finset_of_infinite, lift_id]

lemma stage_exists (hsep : almostDisjointSeparationNumber = 2 ^ ℵ₀)
    (hsplit : R0.splittingNumber = 2 ^ ℵ₀)
    (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : #B < 2 ^ ℵ₀) (x : ι) (hx : #(Set.Iio x) < 2 ^ ℵ₀)
    (p : Set.Iio x → FIStage) (hA : R0.AlmostDisjoint (oldFamily B x p)) :
    ∃ s, StageOK C X B x p s := by
  classical
  let A := oldFamily B x p
  have hcA : #A < 2 ^ ℵ₀ := (mk_union_le _ _).trans_lt
    (add_lt_of_lt aleph0_le_continuum hB (mk_range_le.trans_lt hx))
  have hcT : #(R0.trace (C x) '' A) < R0.splittingNumber := by
    rw [hsplit]
    exact mk_image_le.trans_lt hcA
  have hn : ¬ R0.Splitting (R0.trace (C x) '' A) :=
    fun h => not_le_of_gt hcT (R0.splittingNumber_le h)
  have hex : ∃ I : Set ℕ, I.Infinite ∧ ∀ a ∈ R0.trace (C x) '' A, ¬ R0.Splits a I := by
    simp only [R0.Splitting] at hn
    push Not at hn
    exact hn
  obtain ⟨I, hI, hIA⟩ := hex
  have hic : #(Set.Iic x) < 2 ^ ℵ₀ := by
    have hi : Set.Iic x ⊆ insert x (Set.Iio x) := by
      intro y hy
      rcases lt_or_eq_of_le hy with h | h
      · exact Or.inr h
      · exact Or.inl h
    exact (mk_le_mk_of_subset hi).trans_lt
      (mk_insert_le.trans_lt (add_one_lt_of_lt aleph0_le_continuum hx))
  let R := requirements C X B x p I
  have hcR : #R < 2 ^ ℵ₀ := (requirements_card_le C X B x p I hA.1).trans_lt
    (add_one_lt_of_lt aleph0_le_continuum (mul_lt_of_lt aleph0_le_continuum hic hcA))
  let Y := insert Set.univ (R ∩ {y | ¬ InIdeal A y})
  have hcY : #Y < almostDisjointSeparationNumber := by
    rw [hsep]
    exact mk_insert_le.trans_lt (add_one_lt_of_lt aleph0_le_continuum
      ((mk_le_mk_of_subset inter_subset_left).trans_lt hcR))
  have hY : ∀ y ∈ Y, ¬ InIdeal A y := by
    rintro y (rfl | hy)
    · exact ideal_proper_of_infinite_ad hA
    · exact hy.2
  obtain ⟨a, ha, haA, haY⟩ := small_positive_extension hA (hsep ▸ hcA) hcY
    ⟨Set.univ, mem_insert _ _⟩ hY
  refine ⟨⟨a, I⟩, ha, haA, hI, ?_, ?_⟩
  · intro b hb hi
    exact not_infinite.mp (fun hd => hIA _ ⟨b, hb, rfl⟩ ⟨hi, hd⟩)
  · intro y hy hp
    exact haY y (Or.inr ⟨hy, hp⟩)

variable [WellFoundedLT ι]

lemma build_stage (hsep : almostDisjointSeparationNumber = 2 ^ ℵ₀)
    (hsplit : R0.splittingNumber = 2 ^ ℵ₀)
    (C : ι → R0.FinSequence ℕ) (X : ι → Set ℕ)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (hcB : #B < 2 ^ ℵ₀)
    (hc : ∀ x : ι, #(Set.Iio x) < 2 ^ ℵ₀) (x : ι) :
    StageOK C X B x (fun y => build C X B y.val) (build C X B x) := by
  classical
  induction x using (wellFounded_lt (α := ι)).induction with
  | h x ih =>
    have hA : R0.AlmostDisjoint (oldFamily B x (fun y => build C X B y.val)) := by
      refine ⟨hB.1.mono subset_union_left, ?_, ?_⟩
      · rintro a (ha | ⟨y, rfl⟩)
        · exact hB.2.1 a ha
        · exact (ih y y.property).1
      · rintro a (ha | ⟨y, rfl⟩) b (hb | ⟨z, rfl⟩) hab
        · exact hB.2.2 a ha b hb hab
        · simpa [inter_comm] using (ih z z.property).2.1 a (Or.inl ha)
        · exact (ih y y.property).2.1 b (Or.inl hb)
        · rcases lt_trichotomy y.val z.val with h | h | h
          · simpa [inter_comm] using (ih z z.property).2.1 _ (Or.inr ⟨⟨y, h⟩, rfl⟩)
          · exact False.elim (hab (congrArg (fun t => (build C X B t).member) h))
          · exact (ih y y.property).2.1 _ (Or.inr ⟨⟨z, h⟩, rfl⟩)
    have hex := stage_exists hsep hsplit C X hcB x (hc x) (fun y => build C X B y.val) hA
    conv_rhs => rw [build, WellFounded.fix_eq]
    exact dif_pos hex ▸ hex.choose_spec

end GeneralConstruction

/-- The full published positive construction, extending every infinite AD
family of size below the continuum. No CH hypothesis is used. -/
theorem exists_fi_mad_extension_of_ap_eq_s_eq_continuum
    (hsep : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ ℵ₀)
    (hsplit : R0.splittingNumber = (2 : Cardinal.{0}) ^ ℵ₀)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B) (hcB : #B < 2 ^ ℵ₀) :
    ∃ M : Set (Set ℕ), B ⊆ M ∧ MAD M ∧ R0.FinIntersecting M := by
  classical
  let ι := ((2 : Cardinal.{0}) ^ ℵ₀).ord.ToType
  have hc (x : ι) : #(Set.Iio x) < (2 : Cardinal.{0}) ^ ℵ₀ := by
    have h := Cardinal.mk_Iio_lt x (by
      change Cardinal.ord (Cardinal.mk (((2 : Cardinal) ^ ℵ₀).ord.ToType)) =
        Ordinal.type (fun a b : ((2 : Cardinal) ^ ℵ₀).ord.ToType => a < b)
      rw [Ordinal.type_toType, Cardinal.mk_toType, Cardinal.card_ord])
    simpa [ι] using h
  let D : R0.FinSequence ℕ := {
    block := fun n => {n}
    finite := fun n => finite_singleton n
    nonempty := fun n => singleton_nonempty n
    disjoint := by intro n m h; exact disjoint_singleton.mpr h }
  letI : Nonempty (Set ℕ × R0.FinSequence ℕ) := ⟨(univ, D)⟩
  have hcard : Cardinal.mk (Set ℕ × R0.FinSequence ℕ) ≤ Cardinal.mk ι := by
    calc
      Cardinal.mk (Set ℕ × R0.FinSequence ℕ) =
          (2 : Cardinal) ^ Cardinal.aleph0 * Cardinal.mk (R0.FinSequence ℕ) := by simp
      _ ≤ (2 : Cardinal) ^ Cardinal.aleph0 * (2 : Cardinal) ^ Cardinal.aleph0 :=
        mul_le_mul_right finSequence_card_le_continuum _
      _ = (2 : Cardinal) ^ Cardinal.aleph0 := Cardinal.mul_eq_self Cardinal.aleph0_le_continuum
      _ = Cardinal.mk ι := by simp only [ι, Cardinal.mk_toType, Cardinal.card_ord]
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hcard
  let tasks : ι → Set ℕ × R0.FinSequence ℕ := Function.invFun e
  have ht : Function.Surjective tasks := by
    intro p
    exact ⟨e p, Function.leftInverse_invFun e.injective p⟩
  have hX : Function.Surjective (fun x => (tasks x).1) := by
    intro X
    obtain ⟨x, hx⟩ := ht (X, D)
    exact ⟨x, congrArg Prod.fst hx⟩
  have hC : Function.Surjective (fun x => (tasks x).2) := by
    intro C
    obtain ⟨x, hx⟩ := ht (univ, C)
    exact ⟨x, congrArg Prod.snd hx⟩
  let C := fun x => (tasks x).2
  let X := fun x => (tasks x).1
  let f := CHConstruction.build C X B
  have hf := GeneralConstruction.build_stage hsep hsplit C X hB hcB hc
  exact ⟨finalFamily B f, subset_union_left, finalFamily_mad C X hB f hf hX,
    finalFamily_fi C X hB f hf hC⟩

/-- The stronger positive theorem used in the manuscript's first corollary. -/
theorem exists_fi_mad_of_ap_eq_s_eq_continuum
    (hsep : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ ℵ₀)
    (hsplit : R0.splittingNumber = (2 : Cardinal.{0}) ^ ℵ₀) : ExistsFIMAD := by
  obtain ⟨M, hM, _, _⟩ := InfinitaryCombinatorics.Formalizations.R0.uniform_nonFinIntersecting_mad
  obtain ⟨B, hBM, hcB, hiB⟩ := hM.1.1.exists_subset_countable_infinite
  have hb : #B < (2 : Cardinal.{0}) ^ ℵ₀ :=
    (Cardinal.le_aleph0_iff_set_countable.mpr hcB).trans_lt (Cardinal.cantor ℵ₀)
  obtain ⟨K, _, hK, hFI⟩ := exists_fi_mad_extension_of_ap_eq_s_eq_continuum hsep hsplit
    ⟨hiB, ADFamily.mono hM.1.2 hBM⟩ hb
  exact ⟨K, hK, hFI⟩

/-- The exact equivalence on the section ap = continuum. -/
theorem exists_fi_mad_iff_s_eq_continuum_of_ap_eq_continuum
    (hsep : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ ℵ₀) :
    ExistsFIMAD ↔ R0.splittingNumber = (2 : Cardinal.{0}) ^ ℵ₀ := by
  constructor
  · intro h
    exact le_antisymm splittingNumber_le_continuum (hsep ▸ fi_mad_implies_ap_le_s h)
  · exact exists_fi_mad_of_ap_eq_s_eq_continuum hsep

end InfinitaryCombinatorics.Formalizations.FIMAD

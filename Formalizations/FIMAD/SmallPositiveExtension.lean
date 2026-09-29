import Formalizations.FIMAD.PositiveExtension
import Formalizations.FIMAD.OmegaSplitting
import Formalizations.R0.LocalGlobal

/-! Refinement and positive extension below the separation cardinal. -/

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal
open InfinitaryCombinatorics.Formalizations.R0

/-- A family of fewer than b infinite sets has an indexed AD refinement.
Uniform trace coding supplies finite blocks meeting every set eventually;
distinct branches select almost disjoint collections of those blocks. -/
theorem ad_refinement_below_b {Y : Set (Set ℕ)}
    (hc : #Y < boundingNumber) (hY : ∀ y ∈ Y, y.Infinite) :
    ∃ b : Y → Set ℕ, (∀ y, (b y).Infinite ∧ b y ⊆ y.val) ∧
      ∀ y z, y ≠ z → (b y ∩ b z).Finite := by
  classical
  obtain ⟨C, hC⟩ := uniform_trace_coding Y (bounding_of_card_lt hc)
    (fun _ => univ) (fun _ => univ) (fun _ => infinite_univ)
    (fun y _ => by simpa using hY y y.property)
  have hhit : ∀ y : Y, ∃ N, ∀ n ≥ N, ∃ x, x ∈ y.val ∧ x ∈ C.block n := by
    intro y
    obtain ⟨N, hN⟩ := hC y
    exact ⟨N, fun n hn => (hN n hn).mpr (mem_univ n)⟩
  choose N hN using hhit
  have hbound : #Y ≤ #(Set ℕ) := by
    simpa using hc.le.trans
      (boundingNumber_le_almostDisjointnessNumber.trans almostDisjointnessNumber_le_continuum)
  obtain ⟨e⟩ := (Cardinal.le_def Y (Set ℕ)).mp hbound
  let S (y : Y) : Set ℕ := _root_.R0.nodeEquivNat '' branch (e y)
  have hSi (y) : (S y).Infinite := (branch_infinite (e y)).image _root_.R0.nodeEquivNat.injective.injOn
  have hSad (y z : Y) (hne : y ≠ z) : (S y ∩ S z).Finite := by
    rw [← image_inter _root_.R0.nodeEquivNat.injective]
    exact (branch_inter_finite (fun h => hne (e.injective h))).image _
  let T (y : Y) : Set ℕ := S y \ Set.Iio (N y)
  have hTi (y) : (T y).Infinite := (hSi y).diff (finite_lt_nat _)
  let p (y : Y) (n : T y) : ℕ := (hN y n (Nat.le_of_not_gt n.property.2)).choose
  have hp (y : Y) (n : T y) : p y n ∈ y.val ∧ p y n ∈ C.block n :=
    (hN y n (Nat.le_of_not_gt n.property.2)).choose_spec
  have hindex {y z : Y} {n : T y} {m : T z} (h : p y n = p z m) : n.val = m.val := by
    by_contra hne
    exact Set.disjoint_left.mp (C.disjoint n m hne) (hp y n).2 (h ▸ (hp z m).2)
  have hpi (y) : Function.Injective (p y) := fun _ _ h => Subtype.ext (hindex h)
  refine ⟨fun y => range (p y), fun y => ⟨?_, ?_⟩, ?_⟩
  · letI := (hTi y).to_subtype
    exact infinite_range_of_injective (hpi y)
  · rintro x ⟨n, rfl⟩
    exact (hp y n).1
  · intro y z hne
    apply ((hSad y z hne).biUnion (fun n _ => C.finite n)).subset
    rintro x ⟨⟨n, rfl⟩, ⟨m, hm⟩⟩
    have heq := hindex hm.symm
    exact mem_iUnion₂.mpr ⟨n.val, ⟨n.property.1, heq ▸ m.property.1⟩, (hp y n).2⟩

/-- A positive set contains an infinite set orthogonal to a family of size
below a. The restriction family is considered on the actual subtype Y. -/
theorem positive_subset_below_a {A : Set (Set ℕ)} {Y : Set ℕ}
    (hA : ADFamily A) (hc : #A < almostDisjointnessNumber)
    (hY : ¬ InIdeal A Y) :
    ∃ Z : Set ℕ, Z ⊆ Y ∧ Z.Infinite ∧ ∀ a ∈ A, (Z ∩ a).Finite := by
  classical
  by_contra hn
  have hmeet : ∀ Z : Set ℕ, Z ⊆ Y → Z.Infinite → ∃ a ∈ A, (Z ∩ a).Infinite := by
    intro Z hZY hi
    by_contra hm
    apply hn
    refine ⟨Z, hZY, hi, ?_⟩
    intro a ha
    exact not_infinite.mp (fun h => hm ⟨a, ha, h⟩)
  let R := restriction A Y
  have hR := restriction_ad hA Y
  have hYi : Y.Infinite := fun hf => hY (inIdeal_of_finite A hf)
  by_cases hRf : R.Finite
  · have hw : ∀ p : R, ∃ a ∈ A, p.val = a ∩ Y := fun p => p.property.2
    choose a ha he using hw
    let F := range a
    letI := hRf.fintype
    have hF : F.Finite := finite_range a
    have hFA : F ⊆ A := by rintro _ ⟨p, rfl⟩; exact ha p
    apply hY
    refine ⟨F, hF, hFA, ?_⟩
    by_contra hrem
    obtain ⟨b, hb, hi⟩ := hmeet (Y \ ⋃ x ∈ F, x) diff_subset (not_finite.mp hrem)
    have hbi : (b ∩ Y).Infinite := hi.mono (fun _ hx => ⟨hx.2, hx.1.1⟩)
    let p : R := ⟨b ∩ Y, hbi, b, hb, rfl⟩
    have hpa : b ∩ Y ⊆ a p := by
      have hh := he p
      change b ∩ Y = a p ∩ Y at hh
      rw [hh]
      exact inter_subset_left
    exact hi (finite_empty.subset (fun x hx =>
      (hx.1.2 (mem_iUnion₂.mpr ⟨a p, mem_range_self p, hpa ⟨hx.2, hx.1.1⟩⟩)).elim))
  · letI := hYi.to_subtype
    let v : Y → ℕ := Subtype.val
    let Q : Set (Set Y) := (fun p => v ⁻¹' p) '' R
    have hinj : Set.InjOn (fun p => v ⁻¹' p) R := by
      intro p hp q hq he
      ext x
      constructor
      · intro hx
        have hx' : (⟨x, restriction_subset hp hx⟩ : Y) ∈ v ⁻¹' p := hx
        exact (Set.ext_iff.mp he ⟨x, restriction_subset hp hx⟩).mp hx'
      · intro hx
        have hx' : (⟨x, restriction_subset hq hx⟩ : Y) ∈ v ⁻¹' q := hx
        exact (Set.ext_iff.mp he ⟨x, restriction_subset hq hx⟩).mpr hx'
    have hQ : MAD Q := by
      refine ⟨⟨(not_finite.mp hRf).image hinj, ?_, ?_⟩, ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact hp.1.preimage (fun x hx => ⟨⟨x, restriction_subset hp hx⟩, rfl⟩)
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hpq
        change (v ⁻¹' (p ∩ q)).Finite
        exact (hR.2 p hp q hq (fun he => hpq (he ▸ rfl))).preimage (f := v) Subtype.val_injective.injOn
      · intro Z hZ
        have hi := hZ.image Subtype.val_injective.injOn
        obtain ⟨a, ha, hai⟩ := hmeet (v '' Z)
          (by rintro _ ⟨x, _, rfl⟩; exact x.property) hi
        have har : a ∩ Y ∈ R := ⟨hai.mono (by
          rintro x ⟨⟨z, _, rfl⟩, hx⟩; exact ⟨hx, z.property⟩), a, ha, rfl⟩
        refine ⟨v ⁻¹' (a ∩ Y), ⟨a ∩ Y, har, rfl⟩, ?_⟩
        intro hf
        apply hai
        apply (hf.image v).subset
        rintro x ⟨⟨z, hz, rfl⟩, hza⟩
        exact ⟨z, ⟨hz, hza, z.property⟩, rfl⟩
    have hcard : #Q ≤ #A := Cardinal.mk_image_le.trans (restriction_card_le A Y)
    exact (not_lt_of_ge (mad_card_lower hQ)) (hcard.trans_lt hc)

/-- Simultaneous positive-set hitting at arbitrary stages below ap. -/
theorem small_positive_extension {A Y : Set (Set ℕ)}
    (hA : R0.AlmostDisjoint A) (hcA : #A < almostDisjointSeparationNumber)
    (hcY : #Y < almostDisjointSeparationNumber) (hne : Y.Nonempty)
    (hY : ∀ y ∈ Y, ¬ InIdeal A y) :
    ∃ a : Set ℕ, a.Infinite ∧ (∀ b ∈ A, (a ∩ b).Finite) ∧
      ∀ y ∈ Y, (a ∩ y).Infinite := by
  classical
  have hca : #A < almostDisjointnessNumber := hcA.trans_le
    (almostDisjointSeparationNumber_le_boundingNumber.trans boundingNumber_le_almostDisjointnessNumber)
  have hex (y : Y) := positive_subset_below_a hA.2 hca (hY y y.property)
  choose z hzy hzi hza using hex
  have hcz : #(range z) < boundingNumber := Cardinal.mk_range_le.trans_lt
    (hcY.trans_le almostDisjointSeparationNumber_le_boundingNumber)
  obtain ⟨b, hb, hbb⟩ := ad_refinement_below_b hcz (by rintro _ ⟨y, rfl⟩; exact hzi y)
  let r (y : Y) : Set ℕ := b ⟨z y, mem_range_self y⟩
  let B := range r
  have hr (y) : (r y).Infinite ∧ r y ⊆ y.val :=
    ⟨(hb _).1, (hb _).2.trans (hzy y)⟩
  have hrA (y : Y) (a : Set ℕ) (ha : a ∈ A) : (r y ∩ a).Finite :=
    (hza y a ha).subset (inter_subset_inter_left _ (hb _).2)
  have hBA : Disjoint B A := by
    apply Set.disjoint_left.mpr
    rintro a ⟨y, rfl⟩ ha
    exact (hr y).1 (by simpa using hrA y (r y) ha)
  have hB : ADFamily B := by
    constructor
    · rintro _ ⟨y, rfl⟩; exact (hr y).1
    · rintro _ ⟨y, rfl⟩ _ ⟨w, rfl⟩ hne
      exact hbb _ _ (fun he => hne (congrArg b he))
  have hAB : ADFamily (B ∪ A) := by
    constructor
    · rintro a (ha | ha)
      · exact hB.1 a ha
      · exact hA.2.1 a ha
    · rintro a (ha | ha) c (hc | hc) hne
      · exact hB.2 a ha c hc hne
      · obtain ⟨y, rfl⟩ := ha; exact hrA y c hc
      · obtain ⟨y, rfl⟩ := hc; simpa [inter_comm] using hrA y a ha
      · exact hA.2.2 a ha c hc hne
  have hinf : ℵ₀ ≤ almostDisjointSeparationNumber :=
    (Cardinal.aleph0_le_mk_iff.mpr hA.1.to_subtype).trans hcA.le
  have hcAB : #(B ∪ A : Set (Set ℕ)) < almostDisjointSeparationNumber :=
    (Cardinal.mk_union_le B A).trans_lt (Cardinal.add_lt_of_lt hinf
      (Cardinal.mk_range_le.trans_lt hcY) hcA)
  obtain ⟨a, ha⟩ := weaklySeparable_of_card_lt hAB hcAB B subset_union_left
  have hh (y : Y) : (a ∩ y.val).Infinite := by
    have h := (ha (r y) (Or.inl (mem_range_self y))).mpr (mem_range_self y)
    exact h.mono (fun _ hx => ⟨hx.2, (hr y).2 hx.1⟩)
  obtain ⟨y, hy⟩ := hne
  refine ⟨a, (hh ⟨y, hy⟩).mono inter_subset_left, ?_, fun y hy => hh ⟨y, hy⟩⟩
  intro c hc
  apply not_infinite.mp
  intro hi
  exact Set.disjoint_left.mp hBA ((ha c (Or.inr hc)).mp (by simpa [inter_comm] using hi)) hc

end InfinitaryCombinatorics.Formalizations.FIMAD

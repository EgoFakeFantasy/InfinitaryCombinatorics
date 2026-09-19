import Formalizations.R0.UniformMAD

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
variable {X : Type}

/-- Equality modulo finite, expressed using the shared finite-error containment. -/
def AlmostEqual (a b : Set X) : Prop := AlmostSubset a b ∧ AlmostSubset b a

lemma AlmostEqual.refl (a : Set X) : AlmostEqual a a :=
  ⟨AlmostSubset.refl a, AlmostSubset.refl a⟩

lemma AlmostEqual.symm {a b : Set X} (h : AlmostEqual a b) : AlmostEqual b a :=
  ⟨h.2, h.1⟩

lemma AlmostEqual.trans {a b c : Set X} (h : AlmostEqual a b) (k : AlmostEqual b c) :
    AlmostEqual a c := ⟨h.1.trans k.1, k.2.trans h.2⟩

lemma AlmostEqual.preimage {Y : Type} {a b : Set Y} (h : AlmostEqual a b)
    {f : X → Y} (hf : Function.Injective f) : AlmostEqual (f ⁻¹' a) (f ⁻¹' b) := by
  constructor
  · simpa only [preimage_diff] using (show (a \ b).Finite from h.1).preimage (f := f) hf.injOn
  · simpa only [preimage_diff] using (show (b \ a).Finite from h.2).preimage (f := f) hf.injOn

lemma AlmostEqual.infinite_iff {a b : Set X} (h : AlmostEqual a b) : a.Infinite ↔ b.Infinite :=
  ⟨h.1.infinite, h.2.infinite⟩

lemma finite_change_inter {a b a' b' : Set X} (h : (a ∩ b).Finite)
    (ha : AlmostSubset a' a) (hb : AlmostSubset b' b) : (a' ∩ b').Finite := by
  apply ((h.union ha).union hb).subset
  rintro x ⟨hxa', hxb'⟩
  by_cases hxa : x ∈ a
  · by_cases hxb : x ∈ b
    · exact Or.inl (Or.inl ⟨hxa, hxb⟩)
    · exact Or.inr ⟨hxb', hxb⟩
  · exact Or.inl (Or.inr ⟨hxa', hxa⟩)

/-- Simultaneous individual finite changes preserve AD, maximality, and cardinality. -/
theorem finite_change_mad {M : Set (Set X)} (hM : MAD M) (f : M → Set X)
    (hf : ∀ a, AlmostEqual (f a) a.val) :
    MAD (range f) ∧ #(range f) = #M := by
  have hinf (a : M) : (f a).Infinite := (hf a).infinite_iff.mpr (hM.1.2.1 a a.property)
  have hpair (a b : M) (hab : a ≠ b) : (f a ∩ f b).Finite :=
    finite_change_inter (hM.1.2.2 a a.property b b.property (fun h => hab (Subtype.ext h)))
      (hf a).1 (hf b).1
  have hinj : Function.Injective f := by
    intro a b h
    by_contra hab
    have hi := hpair a b hab
    rw [h, inter_self] at hi
    exact hinf b hi
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, Cardinal.mk_range_eq _ hinj⟩
  · letI : Infinite M := hM.1.1.to_subtype
    exact infinite_range_of_injective hinj
  · rintro a ⟨b, rfl⟩; exact hinf b
  · rintro a ⟨b, rfl⟩ c ⟨d, rfl⟩ hac
    exact hpair b d (fun h => hac (h ▸ rfl))
  · intro Y hY
    obtain ⟨a, ha, hi⟩ := hM.2 Y hY
    refine ⟨f ⟨a, ha⟩, mem_range_self _, ?_⟩
    apply (hi.diff (hf ⟨a, ha⟩).2).mono
    intro x hx
    refine ⟨hx.1.1, ?_⟩
    by_contra hn
    exact hx.2 ⟨hx.1.2, hn⟩

/-- A canonical owner makes a countable AD sequence a genuine partition modulo finite. -/
noncomputable def partitionOwner [Countable X] (f : ℕ → Set X) (x : X) : ℕ := by
  classical
  letI : Encodable X := Encodable.ofCountable X
  exact if h : ∃ n, x ∈ f n then Nat.find h else Encodable.encode x

noncomputable def partitionPart [Countable X] (f : ℕ → Set X) (n : ℕ) : Set X :=
  {x | partitionOwner f x = n}

lemma partitionPart_almostEqual [Countable X] (f : ℕ → Set X)
    (hpair : ∀ n m, n ≠ m → (f n ∩ f m).Finite) (n : ℕ) :
    AlmostEqual (partitionPart f n) (f n) := by
  classical
  letI : Encodable X := Encodable.ofCountable X
  constructor
  · have henc : (Encodable.encode ⁻¹' ({n} : Set ℕ) : Set X).Finite :=
      (finite_singleton n).preimage Encodable.encode_injective.injOn
    apply henc.subset
    intro x hx
    by_cases h : ∃ m, x ∈ f m
    · have hn : Nat.find h = n := by simpa [partitionPart, partitionOwner, h] using hx.1
      exact False.elim (hx.2 (hn ▸ Nat.find_spec h))
    · simpa [partitionPart, partitionOwner, h] using hx.1
  · have hfin : (⋃ i ∈ (Finset.range n : Set ℕ), f n ∩ f i).Finite :=
      (Finset.finite_toSet _).biUnion (fun i hi => hpair n i (by
        have := Finset.mem_range.mp hi
        omega))
    apply hfin.subset
    intro x hx
    have h : ∃ i, x ∈ f i := ⟨n, hx.1⟩
    have hle : Nat.find h ≤ n := Nat.find_min' h hx.1
    have hne : Nat.find h ≠ n := by
      intro hn
      exact hx.2 (by simpa [partitionPart, partitionOwner, h] using hn)
    exact mem_iUnion₂.mpr ⟨Nat.find h, Finset.mem_range.mpr (lt_of_le_of_ne hle hne),
      hx.1, Nat.find_spec h⟩

lemma partitionPart_infinite [Countable X] (f : ℕ → Set X)
    (hpair : ∀ n m, n ≠ m → (f n ∩ f m).Finite)
    (hi : ∀ n, (f n).Infinite) (n : ℕ) : (partitionPart f n).Infinite :=
  (partitionPart_almostEqual f hpair n).infinite_iff.mpr (hi n)

lemma partitionPart_disjoint [Countable X] (f : ℕ → Set X) {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (partitionPart f n) (partitionPart f m) := by
  apply Set.disjoint_left.mpr
  intro x hn hm
  exact hnm (hn.symm.trans hm)

lemma partitionPart_cover [Countable X] (f : ℕ → Set X) :
    (⋃ n, partitionPart f n) = (Set.univ : Set X) := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨partitionOwner f x, rfl⟩

/-- Any two countable infinite AD sequences have a bijection matching their
individual members modulo finite. This supplies the partition step in Lemma 6.1. -/
theorem exists_equiv_almostMatching {Y : Type} [Countable X] [Countable Y]
    (f : ℕ → Set X) (g : ℕ → Set Y)
    (hf : ∀ n, (f n).Infinite) (hg : ∀ n, (g n).Infinite)
    (hfp : ∀ n m, n ≠ m → (f n ∩ f m).Finite)
    (hgp : ∀ n m, n ≠ m → (g n ∩ g m).Finite) :
    ∃ e : X ≃ Y, ∀ n, AlmostEqual (e ⁻¹' g n) (f n) := by
  classical
  have he (n : ℕ) : Nonempty (partitionPart f n ≃ partitionPart g n) := by
    letI : Infinite (partitionPart f n) := (partitionPart_infinite f hfp hf n).to_subtype
    letI : Infinite (partitionPart g n) := (partitionPart_infinite g hgp hg n).to_subtype
    infer_instance
  let epart (n : ℕ) : partitionPart f n ≃ partitionPart g n := Classical.choice (he n)
  let e : X ≃ Y := (Equiv.sigmaFiberEquiv (partitionOwner f)).symm.trans
    ((Equiv.sigmaCongrRight epart).trans (Equiv.sigmaFiberEquiv (partitionOwner g)))
  have howner (x : X) : partitionOwner g (e x) = partitionOwner f x :=
    (epart (partitionOwner f x) ⟨x, rfl⟩).property
  have hpre (n : ℕ) : e ⁻¹' partitionPart g n = partitionPart f n := by
    ext x
    change partitionOwner g (e x) = n ↔ partitionOwner f x = n
    rw [howner]
  refine ⟨e, fun n => ?_⟩
  have h1 := ((partitionPart_almostEqual g hgp n).symm.preimage e.injective)
  rw [hpre] at h1
  exact h1.trans (partitionPart_almostEqual f hfp n)

end InfinitaryCombinatorics.Formalizations.R0

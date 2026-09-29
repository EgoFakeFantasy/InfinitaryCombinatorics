import Formalizations.FIMAD.TraceCoding
import InfinitaryCombinatorics.Characteristics

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal

/-- Weak separation uses infinite/finite intersection, not almost containment. -/
def WeaklySeparable (A : Set (Set ℕ)) : Prop :=
  ∀ B ⊆ A, ∃ X : Set ℕ, ∀ a ∈ A, (a ∩ X).Infinite ↔ a ∈ B

def unboundedCardinals : Set Cardinal :=
  {κ | ∃ F : Set (ℕ → ℕ), (¬ ∃ g, ∀ f ∈ F, EventuallyLE f g) ∧ #F = κ}

noncomputable def boundingNumber : Cardinal := sInf unboundedCardinals

lemma unboundedCardinals_nonempty : unboundedCardinals.Nonempty := by
  refine ⟨#(Set.univ : Set (ℕ → ℕ)), Set.univ, ?_, rfl⟩
  rintro ⟨g,hg⟩
  obtain ⟨N,hN⟩ := hg (fun n => g n+1) (mem_univ _)
  have hh : g N+1 ≤ g N := hN N le_rfl
  omega

lemma bounding_of_card_lt {U : Set (Set ℕ)} (h : #U < boundingNumber) : Bounding U := by
  intro f
  have hb : ∃ g, ∀ v ∈ range f, EventuallyLE v g := by
    by_contra hn
    have hc : boundingNumber ≤ #(range f) := csInf_le' ⟨range f,hn,rfl⟩
    exact (not_le_of_gt h) (hc.trans Cardinal.mk_range_le)
  obtain ⟨g,hg⟩ := hb
  exact ⟨g,fun a => hg (f a) (mem_range_self a)⟩

/-- The cardinal of the least AD family with a nonseparable cut.
Existence of such a cut and the comparison with b are separate obligations. -/
def nonseparableCardinals : Set Cardinal :=
  {κ | ∃ A : Set (Set ℕ), ADFamily A ∧ ¬ WeaklySeparable A ∧ #A = κ}

noncomputable def almostDisjointSeparationNumber : Cardinal := sInf nonseparableCardinals

lemma weaklySeparable_of_card_lt {A : Set (Set ℕ)} (hA : ADFamily A)
    (h : #A < almostDisjointSeparationNumber) : WeaklySeparable A := by
  by_contra hn
  exact (not_le_of_gt h) (csInf_le' ⟨A,hA,hn,rfl⟩)

/-- Weak tests with nonempty positive fibers are automatically infinite. -/
theorem coding_of_nonempty_fibers {U : Set (Set ℕ)} (hb : Bounding U)
    (hs : WeaklySeparable U) (S : U → Set ℕ)
    (hne : ∀ n, ∃ a : U, n ∈ S a) :
    ∃ C : R0.FinSequence ℕ, ∀ a : U, EventuallyEqual (R0.trace C a) (S a) := by
  classical
  let B : ℕ → Set (Set ℕ) := fun n => {a | ∃ ha : a ∈ U, n ∈ S ⟨a,ha⟩}
  have hB (n) : B n ⊆ U := fun _ h => h.choose
  have hsep (n) := hs (B n) (hB n)
  choose X hX using hsep
  have hinf (n) : (X n).Infinite := by
    obtain ⟨a,ha⟩ := hne n
    exact ((hX n a a.property).mpr ⟨a.property,ha⟩).mono inter_subset_right
  apply uniform_trace_coding U hb S X hinf
  intro a n
  simpa [B] using hX n a a.property

lemma EventuallyEqual.infinite_inter {s t I : Set ℕ} (h : EventuallyEqual s t)
    (hi : (I ∩ t).Infinite) : (I ∩ s).Infinite := by
  obtain ⟨N,hN⟩ := h
  apply (hi.diff (finite_lt_nat N)).mono
  intro n hn
  exact ⟨hn.1.1, (hN n (Nat.le_of_not_gt hn.2)).mpr hn.1.2⟩

lemma EventuallyEqual.finite_inter_complement {s t u : Set ℕ}
    (h : EventuallyEqual s u) (h' : EventuallyEqual t uᶜ) : (s ∩ t).Finite := by
  obtain ⟨N,hN⟩ := h
  obtain ⟨M,hM⟩ := h'
  apply (finite_lt_nat (max N M)).subset
  intro n hn
  by_contra hnot
  have hn' := Nat.le_of_not_gt hnot
  exact (hM n ((le_max_right _ _).trans hn')).mp hn.2
    ((hN n ((le_max_left _ _).trans hn')).mp hn.1)

lemma not_centered_of_finite_inter {T : Set (Set ℕ)} {s t : Set ℕ}
    (hs : s ∈ T) (ht : t ∈ T) (hf : (s ∩ t).Finite) : ¬ R0.Centered T := by
  intro hc
  have hsub : ({s,t} : Set (Set ℕ)) ⊆ T := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · exact hs
    · exact mem_singleton_iff.mp hx ▸ ht
  have hh := hc {s,t} hsub (by simp) (by simp)
  have hi : (s ∩ t).Infinite := by simpa using hh
  exact hi hf

/-- The quantitative obstruction, before using the external comparison ap ≤ b. -/
theorem not_finIntersecting_of_large {M : Set (Set ℕ)} (hM : ADFamily M)
    (hsize : R0.splittingNumber ≤ #M)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber)
    (hbound : R0.splittingNumber < boundingNumber) : ¬ R0.FinIntersecting M := by
  classical
  obtain ⟨S,hS,hSc⟩ := R0.exists_minimal_splitting
  have hω : ℵ₀ ≤ #S := hSc ▸ R0.aleph0_le_splittingNumber
  have htwo : (2 : Cardinal) ≤ #S := (Cardinal.natCast_lt_aleph0 (n := 2)).le.trans hω
  have hprod : #(S × Bool) = R0.splittingNumber := by
    simp only [Cardinal.mk_prod,Cardinal.mk_bool,Cardinal.lift_id]
    exact (Cardinal.mul_eq_left hω htwo (by simp)).trans hSc
  obtain ⟨e⟩ := (Cardinal.le_def (S × Bool) M).mp (show #(S × Bool) ≤ #M from hprod ▸ hsize)
  let f : S × Bool → Set ℕ := fun p => (e p).val
  have hfi : Function.Injective f := fun p q h => e.injective (Subtype.ext h)
  let U : Set (Set ℕ) := range f
  have hUM : U ⊆ M := by rintro _ ⟨p,rfl⟩; exact (e p).property
  have hUc : #U = R0.splittingNumber := (Cardinal.mk_range_eq f hfi).trans hprod
  let idx (a : U) : S × Bool := Classical.choose a.property
  have hidx (a : U) : f (idx a) = a.val := Classical.choose_spec a.property
  have idx_f (p : S × Bool) : idx ⟨f p,mem_range_self p⟩ = p := hfi (hidx _)
  let labels : U → Set ℕ := fun a => if (idx a).2 then (idx a).1.valᶜ else (idx a).1.val
  have hlabels (p : S × Bool) : labels ⟨f p,mem_range_self p⟩ =
      if p.2 then p.1.valᶜ else p.1.val := by simp only [labels,idx_f]
  have hne (n) : ∃ a : U, n ∈ labels a := by
    obtain ⟨s,hs⟩ := hS.infinite.nonempty
    by_cases hn : n ∈ s
    · refine ⟨⟨f (⟨s,hs⟩,false),mem_range_self _⟩,?_⟩
      simpa [hlabels] using hn
    · refine ⟨⟨f (⟨s,hs⟩,true),mem_range_self _⟩,?_⟩
      simpa [hlabels] using hn
  obtain ⟨C,hC⟩ := coding_of_nonempty_fibers
    (bounding_of_card_lt (hUc ▸ hbound))
    (weaklySeparable_of_card_lt (hM.mono hUM) (hUc ▸ hsep)) labels hne
  intro hFI
  obtain ⟨I,hI,hcenter⟩ := hFI C
  obtain ⟨s,hs,hsplit⟩ := hS I hI
  let a : U := ⟨f (⟨s,hs⟩,false),mem_range_self _⟩
  let b : U := ⟨f (⟨s,hs⟩,true),mem_range_self _⟩
  have ha : EventuallyEqual (R0.trace C a) s := by simpa [a,hlabels] using hC a
  have hb : EventuallyEqual (R0.trace C b) sᶜ := by simpa [b,hlabels] using hC b
  have hia := ha.infinite_inter hsplit.1
  have hib := hb.infinite_inter (show (I ∩ sᶜ).Infinite from hsplit.2)
  apply not_centered_of_finite_inter (T := R0.retainedTraces C M I)
    ⟨hia,a,hUM a.property,rfl⟩ ⟨hib,b,hUM b.property,rfl⟩ ?_ hcenter
  exact (ha.finite_inter_complement hb).subset (fun _ h => ⟨h.1.2,h.2.2⟩)

/-- The exact FI cutoff under both small-cardinal hypotheses. -/
theorem finIntersecting_iff_card_lt {A : Set (Set ℕ)} (hA : ADFamily A)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber)
    (hbound : R0.splittingNumber < boundingNumber) :
    R0.FinIntersecting A ↔ #A < R0.splittingNumber := by
  constructor
  · intro hFI
    by_contra h
    exact not_finIntersecting_of_large hA (le_of_not_gt h) hsep hbound hFI
  · exact R0.finIntersecting_of_card_lt A

end InfinitaryCombinatorics.Formalizations.FIMAD

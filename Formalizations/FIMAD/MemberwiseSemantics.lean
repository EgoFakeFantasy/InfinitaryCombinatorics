import InfinitaryCombinatorics.FinIntersection

/-! The finite-member formulation used by the set-theoretic sentence is
equivalent to centeredness of the retained *set of traces*. No injectivity
of the trace map is assumed. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set
universe u

def MemberwiseFI {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ C : R0.FinSequence X, ∃ I : Set ℕ, I.Infinite ∧
    ∀ F : Set (Set X), F ⊆ A → F.Finite → F.Nonempty →
      (∀ a ∈ F, (I ∩ R0.trace C a).Infinite) →
      (I ∩ ⋂ a ∈ F, R0.trace C a).Infinite

theorem centered_retainedTraces_iff {X : Type u} (A : Set (Set X))
    (C : R0.FinSequence X) (I : Set ℕ) :
    R0.Centered (R0.retainedTraces C A I) ↔
      ∀ F : Set (Set X), F ⊆ A → F.Finite → F.Nonempty →
        (∀ a ∈ F, (I ∩ R0.trace C a).Infinite) →
        (I ∩ ⋂ a ∈ F, R0.trace C a).Infinite := by
  classical
  constructor
  · intro h F hFA hF hne hi
    let T := (fun a => I ∩ R0.trace C a) '' F
    have hT : T ⊆ R0.retainedTraces C A I := by
      rintro t ⟨a, ha, rfl⟩
      exact ⟨hi a ha, a, hFA ha, rfl⟩
    have hh := h T hT (hF.image _) (hne.image _)
    apply hh.mono
    intro n hn
    obtain ⟨a, ha⟩ := hne
    refine ⟨(mem_iInter₂.mp hn (I ∩ R0.trace C a) ⟨a, ha, rfl⟩).1, ?_⟩
    exact mem_iInter₂.mpr fun b hb =>
      (mem_iInter₂.mp hn (I ∩ R0.trace C b) ⟨b, hb, rfl⟩).2
  · intro h T hT hTf hTne
    letI := hTf.to_subtype
    have hw (t : T) : ∃ a ∈ A, t.val = I ∩ R0.trace C a := (hT t.property).2
    choose a ha hta using hw
    let F : Set (Set X) := range a
    have hFA : F ⊆ A := by
      rintro b ⟨t, rfl⟩
      exact ha t
    have hFne : F.Nonempty := by
      obtain ⟨t, ht⟩ := hTne
      exact ⟨a ⟨t, ht⟩, mem_range_self _⟩
    have hi : ∀ b ∈ F, (I ∩ R0.trace C b).Infinite := by
      rintro b ⟨t, rfl⟩
      rw [← hta t]
      exact (hT t.property).1
    apply (h F hFA (finite_range a) hFne hi).mono
    intro n hn
    apply mem_iInter₂.mpr
    intro t ht
    have htEq : t = I ∩ R0.trace C (a ⟨t, ht⟩) := hta ⟨t, ht⟩
    rw [htEq]
    exact ⟨hn.1, mem_iInter₂.mp hn.2 _ (mem_range_self ⟨t, ht⟩)⟩

theorem finIntersecting_iff_memberwise {X : Type u} (A : Set (Set X)) :
    R0.FinIntersecting A ↔ MemberwiseFI A := by
  simp only [R0.FinIntersecting, MemberwiseFI, centered_retainedTraces_iff]

end InfinitaryCombinatorics.Formalizations.FIMAD

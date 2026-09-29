import Formalizations.FIMAD.Nonexistence
import Formalizations.R0.UniformMAD

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal

lemma nonseparableCardinals_nonempty : nonseparableCardinals.Nonempty := by
  classical
  obtain ⟨M,hM,hMc,_⟩ := InfinitaryCombinatorics.Formalizations.R0.uniform_nonFinIntersecting_mad
  have hn : ¬ WeaklySeparable M := by
    intro h
    have hx (B : Set M) : ∃ X : Set ℕ, ∀ a : M, (a.val ∩ X).Infinite ↔ a ∈ B := by
      obtain ⟨X,hX⟩ := h (Subtype.val '' B) (by rintro _ ⟨a,_,rfl⟩; exact a.property)
      refine ⟨X,?_⟩
      intro a
      simpa only [Subtype.val_injective.mem_set_image] using hX a a.property
    choose X hX using hx
    have hi : Function.Injective X := by
      intro B D heq
      ext a
      rw [← hX B a,heq,hX D a]
    have hc : #(Set M) ≤ #(Set ℕ) := Cardinal.mk_le_of_injective hi
    have hh : (2 : Cardinal) ^ #M ≤ (2 : Cardinal) ^ ℵ₀ := by simpa using hc
    rw [hMc] at hh
    exact (not_le_of_gt (Cardinal.cantor (2 ^ ℵ₀))) hh
  exact ⟨#M,M,hM.1.2,hn,rfl⟩

lemma exists_minimum_nonseparable :
    ∃ A : Set (Set ℕ), ADFamily A ∧ ¬ WeaklySeparable A ∧
      #A = almostDisjointSeparationNumber := csInf_mem nonseparableCardinals_nonempty

end InfinitaryCombinatorics.Formalizations.FIMAD

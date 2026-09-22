import Formalizations.A2.Basic
import Mathlib.Data.Fin.VecNotation

/-! Fixed-colour clique constructors, retaining membership in the prescribed cone. -/
namespace InfinitaryCombinatorics.Formalizations.A2

theorem clique3_of_edges {V K : Type*} (c : PairColoring V K) {x y z : V} {k : K}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h₁ : c.color x y = k) (h₂ : c.color y z = k) (h₃ : c.color x z = k) :
    c.HasClique 3 := by
  let f : Fin 3 → V := ![x, y, z]
  have hi : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨f, hi⟩, k, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [f, c.symm]

theorem clique4_in {V K : Type*} (c : PairColoring V K) (m : K)
    {A B T : Set V} (hdisj : Disjoint A B) (hAT : A ⊆ T) (hBT : B ⊆ T)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, c.color a b = m)
    (hA : ∃ a₀ ∈ A, ∃ a₁ ∈ A, a₀ ≠ a₁ ∧ c.color a₀ a₁ = m)
    (hB : ∃ b₀ ∈ B, ∃ b₁ ∈ B, b₀ ≠ b₁ ∧ c.color b₀ b₁ = m) :
    ∃ e : Fin 4 ↪ V, (∀ i, e i ∈ T) ∧ ∀ i j, i ≠ j → c.color (e i) (e j) = m := by
  obtain ⟨a, ha, a', ha', b, hb, b', hb', haa, hbb, hab, hab', ha'b, ha'b',
    h₁, h₂, h₃, h₄, h₅, h₆⟩ := lemma_3_1 c m hdisj hcross hA hB
  let f : Fin 4 → V := ![a, a', b, b']
  have hi : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f]
  refine ⟨⟨f, hi⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;> dsimp [f]
    · exact hAT ha
    · exact hAT ha'
    · exact hBT hb
    · exact hBT hb'
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, c.symm]

end InfinitaryCombinatorics.Formalizations.A2

import Formalizations.R0.UniformMAD
import Formalizations.R0.Remainder

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

/-- Splitting branches into their two supports preserves the entire orthogonal class. -/
theorem treeFamily_orthogonal (S : Set (Set ℕ)) :
    Orthogonal (treeFamily S) = Orthogonal (branch '' S) := by
  ext Y
  constructor
  · intro h a ha
    obtain ⟨s, hs, rfl⟩ := ha
    have hf (b : Bool) : (Y ∩ half s b).Finite := h _ ⟨(⟨s, hs⟩, b), rfl⟩
    rw [branch_eq_halves, inter_union_distrib_left]
    exact (hf false).union (hf true)
  · rintro h a ⟨⟨s, b⟩, rfl⟩
    apply (h (branch s) ⟨s, s.property, rfl⟩).subset
    rintro x ⟨hxY, n, _, rfl⟩
    exact ⟨hxY, n, rfl⟩

/-- The standard seed and its full branches have exactly the same extension cost. -/
theorem treeFamily_extensionCost (S : Set (Set ℕ)) (U : Set Node) :
    extensionCost (treeFamily S) U = extensionCost (branch '' S) U :=
  extensionCost_orthogonal_invariance (treeFamily_orthogonal S) U

end InfinitaryCombinatorics.Formalizations.R0

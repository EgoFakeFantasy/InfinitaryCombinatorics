import Formalizations.A2.Check

/-! Complete entry point for the paper and its explicit boundary examples. -/
namespace InfinitaryCombinatorics.Formalizations.A2
universe u

/-- Corollary 3.2, proved under the weaker ordinal-length hypothesis. -/
theorem corollary_3_2 (κ : Ordinal.{u}) (hκ : Ordinal.omega0 < κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)) (hc : DeltaRegressive κ c) :
    c.HasClique 4 := by
  obtain ⟨k, _, e, _, he⟩ := theorem_2_2 κ hκ c hc
  exact ⟨e, k, he⟩

end InfinitaryCombinatorics.Formalizations.A2

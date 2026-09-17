import InfinitaryCombinatorics.CountableSplitting
import InfinitaryCombinatorics.FinIntersection

namespace InfinitaryCombinatorics
open Set Cardinal

/-- Countability alone suffices: no AD hypothesis and no restriction on the base type. -/
theorem finIntersecting_of_countable {X : Type*} (A : Set (Set X)) (hA : A.Countable) :
    R0.FinIntersecting A := by
  apply R0.finIntersecting_of_nonsplitting_traces
  intro C hS
  exact Splitting_not_countable hS (hA.image (R0.trace C))

theorem aleph_one_le_splittingNumber : ℵ₁ ≤ R0.splittingNumber :=
  Cardinal.aleph_one_le_iff.mpr aleph0_lt_splittingNumber

theorem splittingNumber_le_continuum : R0.splittingNumber ≤ 2 ^ ℵ₀ := by
  have h := R0.splittingNumber_le R0.splitting_univ
  simpa using h

end InfinitaryCombinatorics

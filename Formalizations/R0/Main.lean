import InfinitaryCombinatorics

/-!
R0 as a problem formalization using the repository's shared definitions and proofs.
The original full proof remains in `R0/`; these public entry points do not change
its hypotheses, its underlying natural numbers, or its cardinality conclusion.
-/

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal

/-- The lower bound does not need an almost disjointness hypothesis. -/
theorem small_families_are_finIntersecting {X : Type} (A : Set (Set X))
    (hA : #A < _root_.R0.splittingNumber) : _root_.R0.FinIntersecting A :=
  _root_.R0.finIntersecting_of_card_lt A hA

/-- Attainment on Nat, including an infinite family of infinite sets. -/
theorem exists_counterexample_of_size_s :
    ∃ A : Set (Set ℕ), _root_.R0.AlmostDisjoint A ∧
      ¬ _root_.R0.FinIntersecting A ∧ #A = _root_.R0.splittingNumber :=
  _root_.R0.exists_non_finIntersecting_ad_of_size_splittingNumber

/-- Membership and minimality, rather than only an equality of infima. -/
theorem least_counterexample_cardinal :
    IsLeast {κ : Cardinal | ∃ A : Set (Set ℕ),
      _root_.R0.AlmostDisjoint A ∧ ¬ _root_.R0.FinIntersecting A ∧ #A = κ}
      _root_.R0.splittingNumber :=
  _root_.R0.splittingNumber_isLeast

/-- The R0 equality, exposed through the problem-formalization entry point. -/
theorem nonFinIntersectingNumber_eq_splittingNumber :
    _root_.R0.nonFinIntersectingNumber = _root_.R0.splittingNumber :=
  _root_.R0.nonFinIntersectingNumber_eq_splittingNumber

end InfinitaryCombinatorics.Formalizations.R0

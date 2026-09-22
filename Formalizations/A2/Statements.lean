import Mathlib.SetTheory.Ordinal.Basic
import InfinitaryCombinatorics.Delta
import InfinitaryCombinatorics.PairColoring
import Formalizations.A2.Basic

/-! Exact, universe-polymorphic acceptance statements for the paper.
The proofs are exported by `Formalizations.A2.Paper`. -/
namespace InfinitaryCombinatorics.Formalizations.A2

open Set
universe u

theorem zero_lt_of_omega_lt {κ : Ordinal} (hκ : Ordinal.omega0 < κ) :
    (0 : Ordinal) < κ :=
  lt_of_le_of_lt bot_le hκ

def Theorem22.{v} : Prop :=
  ∀ (κ : Ordinal.{v}) (hκ : Ordinal.omega0.{v} < κ)
    (c : PairColoring (Branch κ) (Set.Iio κ)),
    DeltaRegressive κ c →
      ∃ k : Set.Iio κ, k.val < Ordinal.omega0.{v} ∧
        ∃ e : Fin 4 ↪ Branch κ,
          (∀ i, e i ∈ zeroCone κ (zero_lt_of_omega_lt hκ)) ∧
          ∀ i j, i ≠ j → c.color (e i) (e j) = k

def Theorem23.{v} : Prop :=
  ∃ c : PairColoring (Branch (Ordinal.omega0.{v} + 1)) (Set.Iio (Ordinal.omega0.{v} + 1)),
    DeltaRegressive (Ordinal.omega0.{v} + 1) c ∧ ¬ c.HasClique 5 ∧ c.HasClique 4

def Theorem24.{v} : Prop :=
  ∀ c : PairColoring (Branch Ordinal.omega0.{v}) (Set.Iio Ordinal.omega0.{v}),
    DeltaRegressive Ordinal.omega0.{v} c → c.HasClique 3

def Proposition53.{v} : Prop :=
  ∃ c : PairColoring (Branch Ordinal.omega0.{v}) (Set.Iio (Ordinal.omega0.{v} + 1)),
    (∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (c.color x y).val < (delta x y hxy).val) ∧
    ¬ c.HasClique 3

end InfinitaryCombinatorics.Formalizations.A2

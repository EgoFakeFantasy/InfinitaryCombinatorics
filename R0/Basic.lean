import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Fin-intersecting families and splitting families

The semantic specification is the R0 review manuscript, Sections 2-4.
Finite traces are removed before centeredness is tested. A fin-sequence
has no uniform finite bound on its block sizes.
-/

namespace R0

open Set Cardinal

universe u

def Splits (s i : Set ℕ) : Prop := (i ∩ s).Infinite ∧ (i \ s).Infinite

/-- Finite and cofinite members are allowed here, but split no infinite set.
Their removal will be proved not to affect splitting or the minimum cardinal. -/
def Splitting (S : Set (Set ℕ)) : Prop :=
  ∀ i : Set ℕ, i.Infinite → ∃ s ∈ S, Splits s i

def AlmostDisjoint {X : Type u} (A : Set (Set X)) : Prop :=
  A.Infinite ∧ (∀ a ∈ A, a.Infinite) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite

structure FinSequence (X : Type u) where
  block : ℕ → Set X
  finite : ∀ n, (block n).Finite
  nonempty : ∀ n, (block n).Nonempty
  disjoint : ∀ n m, n ≠ m → Disjoint (block n) (block m)

def trace {X : Type u} (C : FinSequence X) (a : Set X) : Set ℕ :=
  {n | (a ∩ C.block n).Nonempty}

def retainedTraces {X : Type u} (C : FinSequence X) (A : Set (Set X))
    (i : Set ℕ) : Set (Set ℕ) :=
  {t | t.Infinite ∧ ∃ a ∈ A, t = i ∩ trace C a}

/-- Every nonempty finite subfamily has infinite intersection.
The empty family is centered. -/
def Centered (T : Set (Set ℕ)) : Prop :=
  ∀ F : Set (Set ℕ), F ⊆ T → F.Finite → F.Nonempty → (⋂ t ∈ F, t).Infinite

def FinIntersecting {X : Type u} (A : Set (Set X)) : Prop :=
  ∀ C : FinSequence X, ∃ i : Set ℕ, i.Infinite ∧ Centered (retainedTraces C A i)

end R0

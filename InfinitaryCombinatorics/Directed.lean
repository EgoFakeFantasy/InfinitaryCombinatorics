import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.SetTheory.Cardinal.Order
import Lean.Elab.Tactic.Omega

namespace InfinitaryCombinatorics
universe u v
namespace Directed
variable {V : Type u} {W : Type v}

/-- An injectively enumerated directed cycle, including possible length-one loops. -/
structure Cycle (D : Digraph V) (n : ℕ) where
  positive : 0 < n
  vertex : Fin n ↪ V
  edge : ∀ i : Fin n, D.Adj (vertex i) (vertex ⟨(i.val + 1) % n, Nat.mod_lt _ positive⟩)

def Acyclic (D : Digraph V) : Prop := ∀ n, ¬ Nonempty (Cycle D n)

def NoShortCycles (D : Digraph V) (g : ℕ) : Prop :=
  ∀ n, n < g → ¬ Nonempty (Cycle D n)

def pullback (D : Digraph V) (f : W → V) : Digraph W where
  Adj x y := D.Adj (f x) (f y)

def Cycle.map {D : Digraph V} {E : Digraph W} {n : ℕ} (c : Cycle E n)
    (f : W ↪ V) (hf : ∀ x y, E.Adj x y → D.Adj (f x) (f y)) : Cycle D n where
  positive := c.positive
  vertex := c.vertex.trans f
  edge i := hf _ _ (c.edge i)

theorem acyclic_pullback {D : Digraph V} (hD : Acyclic D) (f : W ↪ V) :
    Acyclic (pullback D f) := by
  rintro n ⟨c⟩
  exact hD n ⟨c.map f (fun _ _ h => h)⟩

theorem noShortCycles_pullback {D : Digraph V} {g : ℕ} (hD : NoShortCycles D g)
    (f : W ↪ V) : NoShortCycles (pullback D f) g := by
  rintro n hn ⟨c⟩
  exact hD n hn ⟨c.map f (fun _ _ h => h)⟩

/-- No colour class contains a directed cycle. -/
def IsDicoloring {K : Type*} (D : Digraph V) (c : V → K) : Prop :=
  ∀ n (p : Cycle D n), ¬ ∃ k, ∀ i, c (p.vertex i) = k

theorem isDicoloring_pullback {K : Type*} {D : Digraph V} {c : V → K}
    (hc : IsDicoloring D c) (f : W ↪ V) : IsDicoloring (pullback D f) (c ∘ f) := by
  intro n p h
  exact hc n (p.map f (fun _ _ h => h)) h

theorem acyclic_iff_dicoloring_unit (D : Digraph V) :
    Acyclic D ↔ IsDicoloring D (fun _ => ()) := by
  constructor
  · intro h n p
    exact (h n ⟨p⟩).elim
  · rintro h n ⟨p⟩
    exact h n p ⟨(), fun _ => rfl⟩

/-- Every induced colour class is acyclic: the usual definition of a dicoloring. -/
theorem isDicoloring_iff_fibers {K : Type*} (D : Digraph V) (c : V → K) :
    IsDicoloring D c ↔ ∀ k, Acyclic (pullback D (fun x : {v // c v = k} => x.val)) := by
  constructor
  · intro h k n hp
    obtain ⟨p⟩ := hp
    let e : {v // c v = k} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    exact h n (p.map e (fun _ _ h => h)) ⟨k, fun i => (p.vertex i).property⟩
  · intro h n p ⟨k, hk⟩
    apply h k n
    exact ⟨{ positive := p.positive
             vertex := ⟨fun i => ⟨p.vertex i, hk i⟩,
               fun _ _ he => p.vertex.injective (congrArg Subtype.val he)⟩
             edge := p.edge }⟩

/-- Cardinal-valued, with both a witness and a lower bound; no finite-colour collapse. -/
def HasDichromaticNumber (D : Digraph V) (κ : Cardinal.{u}) : Prop :=
  (∃ K : Type u, Cardinal.mk K = κ ∧ ∃ c : V → K, IsDicoloring D c) ∧
  ∀ (K : Type u) (c : V → K), IsDicoloring D c → κ ≤ Cardinal.mk K

end Directed
end InfinitaryCombinatorics


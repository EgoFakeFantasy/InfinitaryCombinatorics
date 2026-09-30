import Formalizations.FIMAD.PosetRegular

/-! A shared, mathlib-free contract for countable Boolean splitting tests.
The main package proves the contract for the Dow order; the typed package
uses exactly this contract on actual graph names. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
universe u
variable {P : Type u} (R : Order P)

def NatUnbounded (X : Nat → Prop) : Prop := ∀ N, ∃ k, N ≤ k ∧ X k

def NatSplits (B X : Nat → Prop) : Prop :=
  NatUnbounded (fun k => X k ∧ B k) ∧ NatUnbounded (fun k => X k ∧ ¬ B k)

def enumerationHit (v : Nat → Nat → Regular R) (B : Nat → Prop) (N : Nat) : Regular R :=
  Regular.iSup (fun x : {x : Nat × Nat // N ≤ x.1 ∧ B x.2} => v x.1.1 x.1.2)

/-- This property is proved for Dow forcing, not a logical assumption. Tests
are explicitly indexed by Nat; their infinitude is expressed as unboundedness. -/
def SplittingCertificate : Prop :=
  ∀ v : Nat → Nat → Nat → Regular R,
    (∀ j i, Regular.iSup (v j i) = Regular.top) →
    (∀ j i k, k < i → v j i k = Regular.bot) →
    ∃ tests : Nat → Nat → Prop, (∀ n, NatUnbounded (tests n)) ∧
      ∀ B, (∀ n, NatSplits B (tests n)) → ∀ j N,
        enumerationHit R (v j) B N = Regular.top ∧
        enumerationHit R (v j) (fun k => ¬ B k) N = Regular.top

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

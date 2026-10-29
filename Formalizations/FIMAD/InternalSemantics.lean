import YesMetaZFC.SetTheory.Definitional.Project.Derivation
import YesMetaZFC.SetTheory.Axioms.ZFC

/-! Membership-language meanings for the actual FI MAD existence assertion.
All finiteness, functions, subsets, and sequences in this file are internal to
the structure. In particular, external countability is never substituted for
internal finiteness. No model-existence or preservation assertion is assumed. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Internal
universe u
variable {U : Type u}

/-- `a ⊆ b` for the membership relation `E`. -/
def Subset (E : U → U → Prop) (a b : U) : Prop := ∀ x, E x a → E x b
/-- `a` has no `E`-members. -/
def Empty (E : U → U → Prop) (a : U) : Prop := ∀ x, ¬ E x a
/-- `a` has an `E`-member. -/
def Nonempty (E : U → U → Prop) (a : U) : Prop := ∃ x, E x a
/-- `d` is the intersection of `a` and `b`. -/
def Inter (E : U → U → Prop) (d a b : U) : Prop := ∀ x, E x d ↔ E x a ∧ E x b
/-- `b` is the ordinal successor `a ∪ {a}`. -/
def Succ (E : U → U → Prop) (b a : U) : Prop := ∀ x, E x b ↔ E x a ∨ x = a
/-- `a` contains an empty set and is closed under `Succ`. -/
def Inductive (E : U → U → Prop) (a : U) : Prop :=
  (∃ z, Empty E z ∧ E z a) ∧ ∀ x, E x a → ∃ y, Succ E y x ∧ E y a
/-- `w` is the least inductive set, i.e. the internal `ω`. -/
def Omega (E : U → U → Prop) (w : U) : Prop :=
  Inductive E w ∧ ∀ a, Inductive E a → Subset E w a
/-- `s = {a}`. -/
def Singleton (E : U → U → Prop) (s a : U) : Prop := ∀ x, E x s ↔ x = a
/-- `s = {a, b}`. -/
def UnorderedPair (E : U → U → Prop) (s a b : U) : Prop := ∀ x, E x s ↔ x = a ∨ x = b
/-- `p` is the Kuratowski pair `⟨a, b⟩ = {{a}, {a, b}}`. -/
def Pair (E : U → U → Prop) (p a b : U) : Prop :=
  ∃ s t, Singleton E s a ∧ UnorderedPair E t a b ∧ UnorderedPair E p s t
/-- `f` contains the pair `⟨a, b⟩`, i.e. `f(a) = b`. -/
def Value (E : U → U → Prop) (f a b : U) : Prop := ∃ p, E p f ∧ Pair E p a b
/-- `f` is a set of pairs with first coordinates in `a`, and each `x ∈ a` has exactly one value. -/
def FunctionOn (E : U → U → Prop) (f a : U) : Prop :=
  (∀ p, E p f → ∃ x y, E x a ∧ Pair E p x y) ∧
  ∀ x, E x a → ∃ y, Value E f x y ∧ ∀ z, Value E f x z → z = y
/-- `f` is an injective function from `a` into `b`. -/
def Injection (E : U → U → Prop) (f a b : U) : Prop :=
  FunctionOn E f a ∧ (∀ x y, Value E f x y → E y b) ∧
  ∀ x z y, Value E f x y → Value E f z y → x = z
/-- `a` injects into some element `n` of `w`; with `w = ω` this is internal finiteness. -/
def Finite (E : U → U → Prop) (w a : U) : Prop :=
  ∃ n, E n w ∧ ∃ f, Injection E f a n
/-- `a` is not `Finite` relative to `w`. -/
def Infinite (E : U → U → Prop) (w a : U) : Prop := ¬ Finite E w a
/-- `a ∩ b` exists and is `Infinite` relative to `w`. -/
def InfiniteInter (E : U → U → Prop) (w a b : U) : Prop :=
  ∃ d, Inter E d a b ∧ Infinite E w d
/-- `A` is an infinite almost disjoint family of infinite subsets of `w`. -/
def AD (E : U → U → Prop) (w A : U) : Prop :=
  Infinite E w A ∧ (∀ a, E a A → Subset E a w ∧ Infinite E w a) ∧
  ∀ a b, E a A → E b A → a ≠ b → ∃ d, Inter E d a b ∧ Finite E w d
/-- `A` is `AD` on `w` and every infinite subset of `w` has infinite intersection with some member
of `A`. -/
def MAD (E : U → U → Prop) (w A : U) : Prop :=
  AD E w A ∧ ∀ x, Subset E x w → Infinite E w x → ∃ a, E a A ∧ InfiniteInter E w x a
/-- `C` is a sequence on `w` of pairwise disjoint nonempty finite subsets of `w`. -/
def FinSequence (E : U → U → Prop) (w C : U) : Prop :=
  FunctionOn E C w ∧
  (∀ n b, E n w → Value E C n b → Subset E b w ∧ Finite E w b ∧ Nonempty E b) ∧
  ∀ n m b d, E n w → E m w → n ≠ m → Value E C n b → Value E C m d →
    ¬ ∃ x, E x b ∧ E x d
/-- `n` is in the trace of `a` along `C`: the block `C(n)` meets `a`. -/
def TraceAt (E : U → U → Prop) (C a n : U) : Prop :=
  ∃ b, Value E C n b ∧ ∃ x, E x a ∧ E x b
/-- `t` is the trace of `a` along `C`, restricted to `I`. -/
def RestrictedTrace (E : U → U → Prop) (t C I a : U) : Prop :=
  ∀ n, E n t ↔ E n I ∧ TraceAt E C a n
/-- The trace of `a` along `C`, restricted to `I`, is infinite. -/
def Retained (E : U → U → Prop) (w C I a : U) : Prop :=
  ∃ t, RestrictedTrace E t C I a ∧ Infinite E w t
/-- `t` is the set of `n ∈ I` lying in the trace of every member of `F`. -/
def CommonTrace (E : U → U → Prop) (t C I F : U) : Prop :=
  ∀ n, E n t ↔ E n I ∧ ∀ a, E a F → TraceAt E C a n
/-- `A` is finitely intersecting on `w`: for every block sequence `C` some infinite `I ⊆ w` makes
every nonempty finite subfamily of retained members have an infinite common trace. -/
def FI (E : U → U → Prop) (w A : U) : Prop :=
  ∀ C, FinSequence E w C → ∃ I, Subset E I w ∧ Infinite E w I ∧
    ∀ F, Subset E F A → Finite E w F → Nonempty E F →
      (∀ a, E a F → Retained E w C I a) →
      ∃ t, CommonTrace E t C I F ∧ Infinite E w t
/-- There is an internal `ω` carrying an infinite FI MAD family. -/
def ExistsFIMAD (E : U → U → Prop) : Prop :=
  ∃ w A, Omega E w ∧ MAD E w A ∧ FI E w A

end InfinitaryCombinatorics.Formalizations.FIMAD.Internal

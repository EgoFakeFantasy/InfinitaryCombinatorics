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

def Subset (E : U → U → Prop) (a b : U) : Prop := ∀ x, E x a → E x b
def Empty (E : U → U → Prop) (a : U) : Prop := ∀ x, ¬ E x a
def Nonempty (E : U → U → Prop) (a : U) : Prop := ∃ x, E x a
def Inter (E : U → U → Prop) (d a b : U) : Prop := ∀ x, E x d ↔ E x a ∧ E x b
def Succ (E : U → U → Prop) (b a : U) : Prop := ∀ x, E x b ↔ E x a ∨ x = a
def Inductive (E : U → U → Prop) (a : U) : Prop :=
  (∃ z, Empty E z ∧ E z a) ∧ ∀ x, E x a → ∃ y, Succ E y x ∧ E y a
def Omega (E : U → U → Prop) (w : U) : Prop :=
  Inductive E w ∧ ∀ a, Inductive E a → Subset E w a
def Singleton (E : U → U → Prop) (s a : U) : Prop := ∀ x, E x s ↔ x = a
def UnorderedPair (E : U → U → Prop) (s a b : U) : Prop := ∀ x, E x s ↔ x = a ∨ x = b
def Pair (E : U → U → Prop) (p a b : U) : Prop :=
  ∃ s t, Singleton E s a ∧ UnorderedPair E t a b ∧ UnorderedPair E p s t
def Value (E : U → U → Prop) (f a b : U) : Prop := ∃ p, E p f ∧ Pair E p a b
def FunctionOn (E : U → U → Prop) (f a : U) : Prop :=
  (∀ p, E p f → ∃ x y, E x a ∧ Pair E p x y) ∧
  ∀ x, E x a → ∃ y, Value E f x y ∧ ∀ z, Value E f x z → z = y
def Injection (E : U → U → Prop) (f a b : U) : Prop :=
  FunctionOn E f a ∧ (∀ x y, Value E f x y → E y b) ∧
  ∀ x z y, Value E f x y → Value E f z y → x = z
def Finite (E : U → U → Prop) (w a : U) : Prop :=
  ∃ n, E n w ∧ ∃ f, Injection E f a n
def Infinite (E : U → U → Prop) (w a : U) : Prop := ¬ Finite E w a
def InfiniteInter (E : U → U → Prop) (w a b : U) : Prop :=
  ∃ d, Inter E d a b ∧ Infinite E w d
def AD (E : U → U → Prop) (w A : U) : Prop :=
  Infinite E w A ∧ (∀ a, E a A → Subset E a w ∧ Infinite E w a) ∧
  ∀ a b, E a A → E b A → a ≠ b → ∃ d, Inter E d a b ∧ Finite E w d
def MAD (E : U → U → Prop) (w A : U) : Prop :=
  AD E w A ∧ ∀ x, Subset E x w → Infinite E w x → ∃ a, E a A ∧ InfiniteInter E w x a
def FinSequence (E : U → U → Prop) (w C : U) : Prop :=
  FunctionOn E C w ∧
  (∀ n b, E n w → Value E C n b → Subset E b w ∧ Finite E w b ∧ Nonempty E b) ∧
  ∀ n m b d, E n w → E m w → n ≠ m → Value E C n b → Value E C m d →
    ¬ ∃ x, E x b ∧ E x d
def TraceAt (E : U → U → Prop) (C a n : U) : Prop :=
  ∃ b, Value E C n b ∧ ∃ x, E x a ∧ E x b
def RestrictedTrace (E : U → U → Prop) (t C I a : U) : Prop :=
  ∀ n, E n t ↔ E n I ∧ TraceAt E C a n
def Retained (E : U → U → Prop) (w C I a : U) : Prop :=
  ∃ t, RestrictedTrace E t C I a ∧ Infinite E w t
def CommonTrace (E : U → U → Prop) (t C I F : U) : Prop :=
  ∀ n, E n t ↔ E n I ∧ ∀ a, E a F → TraceAt E C a n
def FI (E : U → U → Prop) (w A : U) : Prop :=
  ∀ C, FinSequence E w C → ∃ I, Subset E I w ∧ Infinite E w I ∧
    ∀ F, Subset E F A → Finite E w F → Nonempty E F →
      (∀ a, E a F → Retained E w C I a) →
      ∃ t, CommonTrace E t C I F ∧ Infinite E w t
def ExistsFIMAD (E : U → U → Prop) : Prop :=
  ∃ w A, Omega E w ∧ MAD E w A ∧ FI E w A

end InfinitaryCombinatorics.Formalizations.FIMAD.Internal

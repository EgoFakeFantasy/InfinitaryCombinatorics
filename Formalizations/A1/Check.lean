import Formalizations.A1.Main
import Formalizations.A1.Partition
import Formalizations.A1.Diamond
import Formalizations.A1.FamilyPrinciple

/-!
# Check file for `Formalizations/A1`

The entries below check the manuscript statements against the delivered
theorems, including the unfolded main conclusion and the full colouring domain.
-/

namespace InfinitaryCombinatorics.Formalizations.A1.Check

open InfinitaryCombinatorics InfinitaryCombinatorics.Formalizations.A1

noncomputable section

/-- Equation (3.1): the Cantor pairing is injective. -/
example {a b c d : ℕ} (h : cantorPair a b = cantorPair c d) : a = c ∧ b = d :=
  cantorPair_inj h

/-- Equation (3.1): `π(a,b) ≥ a`, used for `a_k ≤ k`. -/
example (a b : ℕ) : a ≤ cantorPair a b := le_cantorPair_left a b

/-- The inverse really is the inverse, in both directions. -/
example (a b : ℕ) : cantorFst (cantorPair a b) = a ∧ cantorSnd (cantorPair a b) = b :=
  ⟨cantorFst_pair a b, cantorSnd_pair a b⟩

example (n : ℕ) : cantorPair (cantorFst n) (cantorSnd n) = n := cantorPair_unpair n

/-- §3, equation (3.2): `t_k` is a `DisjointType (k+3)`, i.e. it has width `k+3`. -/
example (k : ℕ) : DisjointType (k + 3) := typeSeq k

/-- §3, Lemma 3.1: every `t_k` has depth exactly one. -/
example (k : ℕ) : (typeSeq k).depth = 1 := typeSeq_depth k

/-- §3: the widths are `k+3`, so the sequence has bounded depth. -/
example : BoundedTypeDepth widthSeq typeSeqW := typeSeqW_boundedDepth

/-- §3, equation (3.3), spelled out for a realization over an arbitrary linear order. -/
example (k : ℕ) {α : Type*} [LinearOrder α] {a b : Fin (k + 3) → α}
    (h : (typeSeq k).Realizes a b) :
    a ⟨jk k, jk_lt_nk k⟩ < b ⟨0, by omega⟩ ∧
    b ⟨0, by omega⟩ < a ⟨jk k + 1, jk_succ_lt_nk k⟩ ∧
    ∀ i : Fin (k + 3), a i < b ⟨1, by omega⟩ := by
  exact typeSeq_order k h

/-- The implementation uses exactly the displayed Cantor formula. -/
example (a b : ℕ) : cantorPair a b = (a + b) * (a + b + 1) / 2 + b :=
  cantorPair_closedForm a b

/-- The full colouring convention leads to the explicit interval-hitting conclusion.
Both type orientations and the original, unthinned prefixes occur in the hypothesis. -/
example (C : CSequence (Ordinal.omega 1))
    (hC : ∀ f : Point → ℕ, ∃ α β : LimitBelow omegaOne, ∃ k,
      α.val < β.val ∧ f (limitPoint α) = k ∧ f (limitPoint β) = k ∧
      ((typeSeq k).Realizes ((C α).initialSegment (k + 3)) ((C β).initialSegment (k + 3)) ∨
       (typeSeq k).swap.Realizes ((C α).initialSegment (k + 3)) ((C β).initialSegment (k + 3)))) :
    ∀ D : Set Point, IsClub D → ∃ β : LimitBelow omegaOne, ∀ m : ℕ, 1 ≤ m →
      ∃ x ∈ D, (C β).seq (3 * m) ≤ x.val ∧ x.val < (C β).seq (3 * m + 3) := by
  have hguess : TypeGuessing C widthSeq typeSeqW :=
    (typeGuessing_iff_allPoints C widthSeq typeSeqW).mpr hC
  intro D hD
  simpa only [Hits, thin_seq, Nat.mul_add, Nat.mul_one] using
    typeGuessing_implies_hits_thin C hguess D hD

/-- The failure hypothesis is the full negation of existence of an interval-hitting system. -/
example
    (h : ¬ ∃ A : LadderSystem, ∀ D : Set Point, IsClub D →
      ∃ β : LimitBelow omegaOne, ∃ N : ℕ, ∀ m ≥ N,
        ∃ x ∈ D, (A β).seq m ≤ x.val ∧ x.val < (A β).seq (m + 1))
    (C : LadderSystem) :
    ∃ f : Point → ℕ, ∀ α β : LimitBelow omegaOne, ∀ k : ℕ,
      f (limitPoint α) = k → f (limitPoint β) = k →
      ¬ ((typeSeq k).Realizes ((C α).initialSegment (k + 3)) ((C β).initialSegment (k + 3)) ∨
         (typeSeq k).swap.Realizes ((C α).initialSegment (k + 3)) ((C β).initialSegment (k + 3))) :=
  antiColoring_on_omegaOne h C

example : (∀ (width : ℕ → ℕ) (t : ∀ k, DisjointType (width k + 1)),
    (∃ d : ℕ, ∀ k, (t k).depth ≤ d) →
    ∃ C : LadderSystem, TypeGuessing C width t) →
    ∃ A : LadderSystem, ∀ D : Set Point, IsClub D →
      ∃ β : LimitBelow omegaOne, ∃ N : ℕ, ∀ m ≥ N,
        ∃ x ∈ D, (A β).seq m ≤ x.val ∧ x.val < (A β).seq (m + 1) :=
  BDTG_implies_KA

example : Diamond → ClubGuessing := Diamond_implies_ClubGuessing
example : KA → KAomegaOne := KA_implies_KAomegaOne

#print axioms cantorPair_closedForm
#print axioms countable_convex_partition
#print axioms typeGuessing_implies_hits_thin
#print axioms typeGuessing_implies_K_thin
#print axioms antiColoring_on_omegaOne
#print axioms BDTG_implies_KA
#print axioms Diamond_implies_ClubGuessing
#print axioms KA_implies_KAomegaOne
end

end InfinitaryCombinatorics.Formalizations.A1.Check

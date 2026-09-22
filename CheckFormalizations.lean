import Formalizations

open Set Cardinal R0

/-- Existence on the actual natural numbers, with the predicates unfolded.
In particular, all infinite retained traces participate in every nonempty
finite intersection test; no predetermined witness family is assumed. -/
example : ∃ A : Set (Set ℕ),
    (A.Infinite ∧ (∀ a ∈ A, a.Infinite) ∧
      ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (a ∩ b).Finite) ∧
    ¬ (∀ C : FinSequence ℕ, ∃ i : Set ℕ, i.Infinite ∧
      ∀ F : Set (Set ℕ),
        (∀ t ∈ F, t.Infinite ∧ ∃ a ∈ A, t = i ∩ {n | (a ∩ C.block n).Nonempty}) →
        F.Finite → F.Nonempty → (⋂ t ∈ F, t).Infinite) ∧
    #A = splittingNumber := by
  simpa only [AlmostDisjoint, FinIntersecting, Centered, retainedTraces,
    trace, Set.subset_def, Set.mem_setOf_eq] using
    InfinitaryCombinatorics.Formalizations.R0.exists_counterexample_of_size_s

example (A : Set (Set ℕ)) (hA : #A < splittingNumber) : FinIntersecting A :=
  InfinitaryCombinatorics.Formalizations.R0.small_families_are_finIntersecting A hA

example : IsLeast {κ : Cardinal | ∃ A : Set (Set ℕ),
    AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = κ} splittingNumber :=
  InfinitaryCombinatorics.Formalizations.R0.least_counterexample_cardinal

example : nonFinIntersectingNumber = splittingNumber :=
  InfinitaryCombinatorics.Formalizations.R0.nonFinIntersectingNumber_eq_splittingNumber

#print axioms InfinitaryCombinatorics.Formalizations.R0.exists_counterexample_of_size_s
#print axioms InfinitaryCombinatorics.Formalizations.R0.nonFinIntersectingNumber_eq_splittingNumber

namespace A1Acceptance
open InfinitaryCombinatorics InfinitaryCombinatorics.Formalizations.A1

example (C : LadderSystem) (h : TypeGuessingOnPoints C widthSeq typeSeqW) :
    ∀ D : Set Point, IsClub D → ∃ β : LimitBelow omegaOne, ∀ m ≥ 1,
      ∃ x ∈ D, (C β).seq (3 * m) ≤ x.val ∧ x.val < (C β).seq (3 * m + 3) := by
  intro D hD
  simpa only [Hits, thin_seq, Nat.mul_add, Nat.mul_one] using
    typeGuessing_implies_hits_thin C ((typeGuessing_iff_allPoints C widthSeq typeSeqW).mpr h) D hD

#print axioms typeGuessing_implies_K_thin
#print axioms antiColoring_on_omegaOne
#print axioms BDTG_implies_KA
#print axioms Diamond_implies_ClubGuessing
#print axioms KA_implies_KAomegaOne
end A1Acceptance

namespace R0PaperAcceptance
open InfinitaryCombinatorics (ADFamily MAD)
open InfinitaryCombinatorics.Formalizations.R0

-- The global construction includes maximality and the actual continuum size.
example : ∃ K : Set (Set ℕ),
    (K.Infinite ∧ (∀ a ∈ K, a.Infinite) ∧
      ∀ a ∈ K, ∀ b ∈ K, a ≠ b → (a ∩ b).Finite) ∧
    (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ K, (Y ∩ a).Infinite) ∧
    #K = 2 ^ ℵ₀ ∧ ¬ FinIntersecting K := by
  obtain ⟨K, hK, hc, hn⟩ := uniform_nonFinIntersecting_mad
  exact ⟨K, hK.1, hK.2, hc, hn⟩

example (κ : Cardinal) :
    (∃ A : Set (Set ℕ), AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = κ) ↔
    splittingNumber ≤ κ ∧ κ ≤ 2 ^ ℵ₀ := nonFinIntersecting_cardinal_spectrum κ

-- Local maximality permits finite families; exact inclusion is retained.
example {F : Set (Set ℕ)} (hF : ADFamily F) (hc : F.Countable) :
    ∃ K : Set (Set ℕ), F ⊆ K ∧ ADFamily K ∧
      (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ K, (Y ∩ a).Infinite) ∧
      #K ≤ almostDisjointnessNumber := by
  obtain ⟨K, hFK, hK, hcard⟩ := countable_completion hF hc
  exact ⟨K, hFK, hK.1, fun Y hY => hK.2.2 Y (subset_univ _) hY, hcard⟩

-- The incidence hypothesis is about the original indexed members of E.
example {E N : Set (Set ℕ)} (hE : AlmostDisjoint E)
    (hEc : #E ≤ almostDisjointnessNumber) (hN : MAD N)
    (hNc : #N = almostDisjointnessNumber)
    (hi : ∀ n ∈ N, {a | a ∈ E ∧ (a ∩ n).Infinite}.Countable)
    (hn : ¬ FinIntersecting E) :
    ∃ K, E ⊆ K ∧ MAD K ∧ #K = almostDisjointnessNumber ∧ ¬ FinIntersecting K :=
  nonFinIntersecting_countable_incidence_transfer hE hEc hN hNc hi hn

-- The assignment S is fixed before the quantifier over every infinite I.
example {M D : Set (Set ℕ)} (hM : MAD M) (hD : D ⊆ M)
    (C : FinSequence ℕ) (S : Set ℕ → Set ℕ)
    (h : ∀ I : Set ℕ, I.Infinite → ∃ a ∈ D,
      (I ∩ ({n | (a ∩ C.block n).Nonempty} ∩ S a)).Infinite ∧
      (I ∩ ({n | (a ∩ C.block n).Nonempty} \ S a)).Infinite) :
    ∃ K : Set (Set ℕ), MAD K ∧ #K = #M ∧ ¬ FinIntersecting K :=
  trace_splitting_replacement hM hD C S h

example {E : Set (Set ℕ)} (hE : AlmostDisjoint E) :
    placementNumber E = max #E (extensionCost E Set.univ) := placement_formula hE

example {H : Type} (C : FinSequence ℕ)
    (hg : ∀ k, ∃ N, ∀ n, N ≤ n → k ≤ blockSize C n)
    (hH : #H ≤ 2 ^ ℵ₀) (U : H → Set (Set ℕ)) (hU : ∀ h, ADFamily (U h)) :
    ∃ A : ((h : H) × U h) → Set ℕ, Function.Injective A ∧ ADFamily (range A) ∧
      ∀ p, trace C (A p) = p.2.val ∧ A p ⊆ ⋃ n, C.block n ∧
        ∀ n, (A p ∩ C.block n).Subsingleton := exact_trace_realization C hg hH U hU

-- These zero-cost instances also guard the finite-local convention.
example {F : Set (Set ℕ)} (hF : MaximalOn F Set.univ) :
    extensionCost F Set.univ = 0 := extensionCost_eq_zero_of_maximal hF

#print axioms exact_trace_realization
#print axioms uniform_nonFinIntersecting_mad
#print axioms countable_completion
#print axioms local_to_global_extension_bounds
#print axioms nonFinIntersecting_countable_incidence_transfer
#print axioms placement_formula
#print axioms trace_splitting_replacement
#print axioms triangle_counterexample
end R0PaperAcceptance

namespace A2PaperAcceptance
open InfinitaryCombinatorics
open InfinitaryCombinatorics.Formalizations.A2
universe u

-- Arbitrary ordinal length: the colour is finite, and all four points lie in the zero cone.
example (κ : Ordinal.{u}) (hκ : Ordinal.omega0 < κ)
    (c : PairColoring (Set.Iio κ → Bool) (Set.Iio κ))
    (hc : ∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (c.color x y).val < (delta x y hxy).val) :
    ∃ k : Set.Iio κ, k.val < Ordinal.omega0 ∧ ∃ e : Fin 4 ↪ (Set.Iio κ → Bool),
      (∀ i, e i ⟨0, zero_lt_of_omega_lt hκ⟩ = false) ∧
      ∀ i j, i ≠ j → c.color (e i) (e j) = k := theorem_2_2 κ hκ c hc

-- The sharp example lives on omega + 1 and has exactly the advertised clique bounds.
example : ∃ c : PairColoring (Set.Iio (Ordinal.omega0.{u} + 1) → Bool)
    (Set.Iio (Ordinal.omega0.{u} + 1)),
    (∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (c.color x y).val < (delta x y hxy).val) ∧
    (¬ ∃ e : Fin 5 ↪ (Set.Iio (Ordinal.omega0.{u} + 1) → Bool),
      ∃ k, ∀ i j, i ≠ j → c.color (e i) (e j) = k) ∧
    (∃ e : Fin 4 ↪ (Set.Iio (Ordinal.omega0.{u} + 1) → Bool),
      ∃ k, ∀ i j, i ≠ j → c.color (e i) (e j) = k) := theorem_2_3

-- The advertised explicit four-clique has colour zero, not only an unspecified colour.
example (i j : Fin 4) (hij : i ≠ j) :
    (sharpColoringC : PairColoring (Branch (Ordinal.omega0.{u} + 1))
      (Set.Iio (Ordinal.omega0.{u} + 1))).color (fourEmbedding i) (fourEmbedding j) =
        ⟨0, zero_lt_omega_add_one⟩ := fourEmbedding_colour_zero i j hij

-- The triangle conclusion retains the original ordinal domain and colour set.
example (c : PairColoring (Set.Iio Ordinal.omega0.{u} → Bool) (Set.Iio Ordinal.omega0.{u}))
    (hc : ∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (c.color x y).val < (delta x y hxy).val) :
    ∃ e : Fin 3 ↪ (Set.Iio Ordinal.omega0.{u} → Bool),
      ∃ k, ∀ i j, i ≠ j → c.color (e i) (e j) = k := theorem_2_4 c hc

-- The maximality lemma is a conclusion, not a premise of the triangle theorem.
example (d : (ℕ → Bool) → ℕ) :
    ∃ x y : ℕ → Bool, ∃ hxy : x ≠ y,
      d x = delta x y hxy ∧ d y = delta x y hxy := delta_maximal d

-- Adding one colour changes the conclusion; the domain remains omega.
example : ∃ c : PairColoring (Set.Iio Ordinal.omega0.{u} → Bool)
    (Set.Iio (Ordinal.omega0.{u} + 1)),
    (∀ x y (hxy : x ≠ y), 0 < (delta x y hxy).val →
      (c.color x y).val < (delta x y hxy).val) ∧
    ¬ (∃ e : Fin 3 ↪ (Set.Iio Ordinal.omega0.{u} → Bool),
      ∃ k, ∀ i j, i ≠ j → c.color (e i) (e j) = k) := proposition_5_3

-- Proposition 4.2 concerns the canonical copy, not the whole longer space.
example {κ : Ordinal.{u}} (hκ : Ordinal.omega0 + 1 ≤ κ) :
    DeltaRegressive κ (canonicalColoring hκ) ∧
    ¬ ((canonicalColoring hκ).pullback (zeroExtend hκ)).HasClique 5 :=
  ⟨canonicalColoring_regressive hκ, canonicalColoring_no_five_on_copy hκ⟩

#print axioms theorem_2_2
#print axioms theorem_2_3
#print axioms theorem_2_4
#print axioms delta_maximal
#print axioms proposition_5_3
#print axioms normalizedPullback_on_zero_cone
#print axioms observation_counterexample
end A2PaperAcceptance

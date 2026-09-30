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

namespace Q410PaperAcceptance
open Set Cardinal InfinitaryCombinatorics InfinitaryCombinatorics.Formalizations.R0

-- The target is an infinite ordinary MAD family on all natural numbers, of exact size a.
-- Non-FI has the original universal fin-sequence definition, without an added oracle.
example (h : _root_.R0.splittingNumber ≤ almostDisjointnessNumber) :
    ∃ M : Set (Set ℕ),
      (M.Infinite ∧ (∀ a ∈ M, a.Infinite) ∧
        ∀ a ∈ M, ∀ b ∈ M, a ≠ b → (a ∩ b).Finite) ∧
      (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ M, (Y ∩ a).Infinite) ∧
      #M = almostDisjointnessNumber ∧
      ¬ (∀ C : _root_.R0.FinSequence ℕ, ∃ I : Set ℕ, I.Infinite ∧
        _root_.R0.Centered (_root_.R0.retainedTraces C M I)) := by
  simpa only [MAD, _root_.R0.AlmostDisjoint, _root_.R0.FinIntersecting, and_assoc] using
    exists_nonFinIntersecting_mad_size_a h

example : (∃ M : Set (Set ℕ), MAD M ∧ #M = almostDisjointnessNumber ∧
    ¬ _root_.R0.FinIntersecting M) ↔ _root_.R0.splittingNumber ≤ almostDisjointnessNumber :=
  nonFinIntersecting_mad_size_a_iff

#print axioms cell_finite_relative_completion
#print axioms predecessor_completion_triangle
#print axioms exists_nonFinIntersecting_mad_size_a
#print axioms nonFinIntersecting_mad_size_a_iff
end Q410PaperAcceptance

namespace FIMADAcceptance
open InfinitaryCombinatorics InfinitaryCombinatorics.Formalizations.FIMAD

-- All candidate families on the actual natural numbers are quantified here.
example (hsep : R0.splittingNumber < almostDisjointSeparationNumber) :
    ¬ ∃ M : Set (Set ℕ),
      (M.Infinite ∧ (∀ a ∈ M, a.Infinite) ∧
        ∀ a ∈ M, ∀ b ∈ M, a ≠ b → (a ∩ b).Finite) ∧
      (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ M, (Y ∩ a).Infinite) ∧
      R0.FinIntersecting M := by
  rintro ⟨M,hAD,hmax,hFI⟩
  exact no_fi_mad_of_s_lt_ap hsep ⟨M,⟨hAD,hmax⟩,hFI⟩

example {A : Set (Set ℕ)} (hA : ADFamily A)
    (hs : R0.splittingNumber < almostDisjointSeparationNumber) :
    R0.FinIntersecting A ↔ #A < R0.splittingNumber :=
  finIntersecting_iff_card_lt_of_s_lt_ap hA hs

example (U : Set (Set ℕ)) (hc : #U < boundingNumber)
    (S : U → Set ℕ) (X : ℕ → Set ℕ) (hX : ∀ n, (X n).Infinite)
    (ht : ∀ a : U, ∀ n, (a.val ∩ X n).Infinite ↔ n ∈ S a) :
    ∃ C : R0.FinSequence ℕ, ∀ a : U, ∃ N, ∀ n ≥ N,
      (a.val ∩ C.block n).Nonempty ↔ n ∈ S a :=
  uniform_trace_coding U (bounding_of_card_lt hc) S X hX ht

#print axioms uniform_trace_coding
#print axioms no_fi_mad_of_s_lt_ap_and_b
#print axioms almostDisjointSeparationNumber_le_boundingNumber
#print axioms exists_fi_mad_of_CH
#print axioms exists_fi_mad_size_aleph_one_of_CH

-- CH is the only hypothesis. In particular, no recursion, positive-extension,
-- maximal-family existence, or FI-preservation result is assumed here.
example (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) :
    ∃ M : Set (Set ℕ),
      (M.Infinite ∧ (∀ a ∈ M, a.Infinite) ∧
        ∀ a ∈ M, ∀ b ∈ M, a ≠ b → (a ∩ b).Finite) ∧
      (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ M, (Y ∩ a).Infinite) ∧
      (∀ C : R0.FinSequence ℕ, ∃ I : Set ℕ, I.Infinite ∧
        R0.Centered {t : Set ℕ | t.Infinite ∧ ∃ a ∈ M, t = I ∩ R0.trace C a}) ∧
      #M = Cardinal.aleph 1 := by
  obtain ⟨M, hM, hFI, hcard⟩ := exists_fi_mad_size_aleph_one_of_CH hCH
  exact ⟨M, hM.1, hM.2, hFI, hcard⟩

-- No recursion or extension lemma is an input: only the two cardinal equations.
example (hap : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0)
    (hs : R0.splittingNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0)
    {B : Set (Set ℕ)} (hB : R0.AlmostDisjoint B)
    (hsize : #B < (2 : Cardinal.{0}) ^ Cardinal.aleph0) :
    ∃ M : Set (Set ℕ), B ⊆ M ∧
      (M.Infinite ∧ (∀ a ∈ M, a.Infinite) ∧
        ∀ a ∈ M, ∀ b ∈ M, a ≠ b → (a ∩ b).Finite) ∧
      (∀ Y : Set ℕ, Y.Infinite → ∃ a ∈ M, (Y ∩ a).Infinite) ∧
      (∀ C : R0.FinSequence ℕ, ∃ I : Set ℕ, I.Infinite ∧
        R0.Centered {t : Set ℕ | t.Infinite ∧ ∃ a ∈ M, t = I ∩ R0.trace C a}) := by
  obtain ⟨M, hBM, hM, hFI⟩ :=
    exists_fi_mad_extension_of_ap_eq_s_eq_continuum hap hs hB hsize
  exact ⟨M, hBM, hM.1, hM.2, hFI⟩

example (hap : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0) :
    (∃ M : Set (Set ℕ), MAD M ∧ R0.FinIntersecting M) ↔
      R0.splittingNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0 :=
  exists_fi_mad_iff_s_eq_continuum_of_ap_eq_continuum hap

#print axioms ad_refinement_below_b
#print axioms small_positive_extension
#print axioms exists_fi_mad_extension_of_ap_eq_s_eq_continuum
#print axioms exists_fi_mad_iff_s_eq_continuum_of_ap_eq_continuum

#print axioms Metatheory.relative_independence

-- This is the actual first-order sentence, with a proved membership semantics.
example {M : YesMetaZFC.SetTheory.Structure}
    (hExt : YesMetaZFC.SetTheory.Extensional M)
    (env : YesMetaZFC.Logic.FirstOrder.Env (Internal.FirstOrderBridge.toFirstOrder M)) :
    YesMetaZFC.Logic.FirstOrder.Formula.satisfies env ModelInterface.existenceSentence ↔
      ∃ w A, Internal.Omega M.mem w ∧ Internal.MAD M.mem w A ∧ Internal.FI M.mem w A :=
  Internal.FirstOrderBridge.satisfies_fimad_sentence hExt env

-- BMZ's configuration is still an explicit input, not a model-existence claim.
example (hs : omegaSplittingNumber = Cardinal.aleph 1)
    (hd : dowNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0)
    (hc : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 2) :
    ¬ ∃ A : Set (Set ℕ), MAD A ∧ R0.FinIntersecting A :=
  (consequences_of_bmz_configuration hs hd hc).2.2.2.2

#print axioms Internal.FirstOrderBridge.satisfies_fimad_sentence
#print axioms ModelInterface.independent_of_models
#print axioms finIntersecting_iff_memberwise
#print axioms consequences_of_bmz_configuration
#print axioms exists_fi_mad_of_a_lt_s

-- The interpretation uses actual membership and agrees at arbitrary universe levels.
example (a : ZFSet.{u}) : Internal.Finite (fun x y => x ∈ y) ZFSet.omega a ↔
    (a : Set ZFSet).Finite := Standard.finite_iff a

example : Internal.ExistsFIMAD (fun x y : ZFSet.{u} => x ∈ y) ↔
    ∃ M : Set (Set ℕ), MAD M ∧ R0.FinIntersecting M := Standard.existsFIMAD_iff

example : ModelInterface.ModelsZFC Standard.model.{u} := Standard.models_zfc

example (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) :
    YesMetaZFC.Logic.FirstOrder.Derives.Consistent ModelInterface.zfcTheory
      [ModelInterface.existenceSentence] := Standard.positive_consistency_of_CH hCH

example (h : R0.splittingNumber < almostDisjointSeparationNumber) :
    YesMetaZFC.Logic.FirstOrder.Derives.Consistent ModelInterface.zfcTheory
      [YesMetaZFC.Logic.FirstOrder.Formula.neg ModelInterface.existenceSentence] :=
  Standard.negative_consistency_of_s_lt_ap h

#print axioms Standard.existsFIMAD_iff
#print axioms Standard.models_zfc
#print axioms Standard.satisfies_sentence_iff
#print axioms Standard.positive_consistency_of_CH
#print axioms Standard.negative_consistency_of_s_lt_ap

-- This is Dow's forbidden-stem forcing, with stronger conditions smaller.
example (A : Set (Set ℕ)) (p q : DowForcing.Condition A) : p ≤ q ↔
    q.stem ⊆ p.stem ∧ q.forbidden ⊆ p.forbidden ∧ p.stem ∉ q.forbidden := Iff.rfl

example (A : Set (Set ℕ)) (S : Set (Finset ℕ)) : DowForcing.Admissible A S ↔
    ∀ s, s ∉ S → ∀ a ∈ A, ∃ n, ∀ t : Finset ℕ,
      (∀ k ∈ t, k ∈ a ∧ n ≤ k) → s ∪ t ∉ S := Iff.rfl

#print axioms DowForcing.sigma_centered
#print axioms DowForcing.antichain_countable
#print axioms DowForcing.hit_dense
#print axioms DowForcing.avoid_dense
#print axioms DowForcing.reach_all
#print axioms DowForcing.unionStems_weaklySeparates
#print axioms DowForcing.countable_tallness_tests
#print axioms DowForcing.simultaneous_splitting_tests

-- The canonical Boolean coefficients really are regularized stem membership.
example (A : Set (Set ℕ)) (k : ℕ) (p : DowForcing.Condition A) :
    (DowForcing.genericValue A k).mem p ↔
      ∀ q, q ≤ p → ∃ r, r ≤ q ∧ k ∈ r.stem := Iff.rfl

-- The negative tail value quantifies over all stronger conditions, with a
-- genuine finite stem as the bound. No generic filter is an input.
example (A : Set (Set ℕ)) (B : Set ℕ) (s : Finset ℕ)
    (p : DowForcing.Condition A) :
    (DowForcing.avoidsOutside (A := A) B s).mem p ↔
      ∀ q, q ≤ p → ¬ (∀ r, r ≤ q → ∃ t, t ≤ r ∧
        ∃ k : {k : ℕ // k ∈ B ∧ k ∉ s},
          ∀ v, v ≤ t → ∃ w, w ≤ v ∧ k.1 ∈ w.stem) := Iff.rfl

#print axioms PosetRegular.Regular.double_neg
#print axioms PosetRegular.Regular.condition_dense
#print axioms DowForcing.generic_hits_top
#print axioms DowForcing.generic_avoids_top
#print axioms DowForcing.boolean_antichain_countable
#print axioms DowForcing.boolean_splitting_tests

-- The exact same source-level contract is consumed by the graph-name adapter.
example (A : Set (Set ℕ)) :
    PosetRegular.SplittingCertificate (DowForcing.forcingOrder A) :=
  DowForcing.splittingCertificate A

example (X : Set ℕ) : PosetRegular.NatUnbounded X ↔ X.Infinite :=
  (DowForcing.infinite_iff_natUnbounded X).symm

#print axioms DowForcing.splittingCertificate
end FIMADAcceptance

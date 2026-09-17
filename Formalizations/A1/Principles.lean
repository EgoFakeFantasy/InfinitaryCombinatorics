import Formalizations.A1.TypeSequence
import Mathlib.SetTheory.Cardinal.Aleph

/-!
# The ambient ordinal and interval-hitting principles

All ladders live on the actual first uncountable ordinal. Club sets use
mathlib's closed-cofinal predicate on its initial segment.
-/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order Ordinal Cardinal

noncomputable section

abbrev omegaOne : Ordinal.{0} := Ordinal.omega 1
abbrev Point := Set.Iio omegaOne
abbrev LadderSystem := CSequence omegaOne

/-- Every proper initial segment of omega one is countable. -/
theorem countable_initialSegment (d : Point) : Countable (Set.Iio d.val) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]
  exact Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp d.property)

theorem point_exists_gt (x : Point) : ∃ y : Point, x < y := by
  refine ⟨⟨Order.succ x.val, (Cardinal.isSuccLimit_omega 1).succ_lt x.property⟩, ?_⟩
  exact Order.lt_succ x.val

/-- A ladder value regarded as a point below omega one. -/
def ladderPoint (C : LadderSystem) (β : LimitBelow omegaOne) (n : ℕ) : Point :=
  ⟨(C β).seq n, ((C β).below n).trans β.property.1⟩

theorem ladderPoint_strictMono (C : LadderSystem) (β : LimitBelow omegaOne) :
    StrictMono (ladderPoint C β) := (C β).increasing

/-- The specified threefold thinning, retaining its cofinality proof. -/
def thin (C : LadderSystem) : LadderSystem := fun β =>
  { seq := fun m => (C β).seq (3 * m)
    increasing := fun _ _ h => (C β).increasing (by omega)
    below := fun m => (C β).below (3 * m)
    cofinal := by
      intro γ hγ
      obtain ⟨i, hi⟩ := (C β).cofinal γ hγ
      exact ⟨i, hi.trans_le ((C β).increasing.monotone (by omega))⟩ }

@[simp] theorem thin_seq (C : LadderSystem) (β : LimitBelow omegaOne) (m : ℕ) :
    (thin C β).seq m = (C β).seq (3 * m) := rfl

/-- A half-open ladder interval meets the given set. -/
def Hits (C : LadderSystem) (D : Set Point) (β : LimitBelow omegaOne) (m : ℕ) : Prop :=
  ∃ x ∈ D, (C β).seq m ≤ x.val ∧ x.val < (C β).seq (m + 1)

/-- Each club is hit eventually at every interval of some ladder. -/
def K (C : LadderSystem) : Prop :=
  ∀ D : Set Point, IsClub D → ∃ β, ∃ N : ℕ, ∀ m ≥ N, Hits C D β m

/-- Kunen's interval-hitting principle for ladder systems. -/
def KA : Prop := ∃ C : LadderSystem, K C

/-- Existence of a system guessing the fixed sequence from Section 3. -/
def G : Prop := ∃ C : LadderSystem, TypeGuessing C widthSeq typeSeqW

/-- Every sequence of positive-width types with uniformly bounded depth has a guessing system. -/
def BDTG : Prop :=
  ∀ (width : ℕ → ℕ) (t : ∀ k, DisjointType (width k + 1)),
    BoundedTypeDepth width t → ∃ C : LadderSystem, TypeGuessing C width t

/-- A limit index viewed in the full domain of ordinal colourings. -/
def limitPoint (β : LimitBelow omegaOne) : Point := ⟨β.val, β.property.1⟩

/-- Extend a colouring of the nonzero limit ordinals by zero elsewhere. -/
def extendColoring (f : LimitBelow omegaOne → ℕ) (x : Point) : ℕ := by
  classical
  exact if h : Order.IsSuccLimit x.val then f ⟨x.val, x.property, h⟩ else 0

@[simp] theorem extendColoring_limit (f : LimitBelow omegaOne → ℕ)
    (β : LimitBelow omegaOne) : extendColoring f (limitPoint β) = f β := by
  simp [extendColoring, limitPoint, β.property.2]

/-- The manuscript convention: the colouring is defined on all of omega one. -/
def TypeGuessingOnPoints (C : LadderSystem) (width : ℕ → ℕ)
    (t : ∀ k, DisjointType (width k + 1)) : Prop :=
  ∀ f : Point → ℕ, ∃ α β : LimitBelow omegaOne, ∃ k,
    α.val < β.val ∧ f (limitPoint α) = k ∧ f (limitPoint β) = k ∧
      ((t k).Realizes ((C α).initialSegment (width k + 1)) ((C β).initialSegment (width k + 1)) ∨
       (t k).swap.Realizes ((C α).initialSegment (width k + 1)) ((C β).initialSegment (width k + 1)))

/-- Restricting colourings to limit indices does not change the guessing principle. -/
theorem typeGuessing_iff_allPoints (C : LadderSystem) (width : ℕ → ℕ)
    (t : ∀ k, DisjointType (width k + 1)) :
    TypeGuessing C width t ↔ TypeGuessingOnPoints C width t := by
  constructor
  · intro h f
    exact h (fun β => f (limitPoint β))
  · intro h f
    obtain ⟨α, β, k, hab, ha, hb, ht⟩ := h (extendColoring f)
    exact ⟨α, β, k, hab, by simpa using ha, by simpa using hb, ht⟩
/-- The same club witnesses failure on arbitrarily late intervals of every ladder. -/
theorem not_K_iff (C : LadderSystem) :
    ¬ K C ↔ ∃ D : Set Point, IsClub D ∧
      ∀ β : LimitBelow omegaOne, ∀ N : ℕ, ∃ m ≥ N, ¬ Hits C D β m := by
  classical
  simp only [K, not_forall, not_exists, exists_prop]

end

end InfinitaryCombinatorics.Formalizations.A1

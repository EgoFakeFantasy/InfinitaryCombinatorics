import Formalizations.A1.Main
import Mathlib.SetTheory.Cardinal.Regular

/-! # Diamond implies club guessing (the internal argument of Lemma 7.2) -/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order Ordinal Cardinal
noncomputable section

/-- Strict unboundedness below a specified ordinal. -/
def UnboundedBelow (s : Set Point) (β : Ordinal.{0}) : Prop :=
  ∀ γ < β, ∃ δ ∈ s, γ < δ.val ∧ δ.val < β

/-- Every unbounded subset of a nonzero countable limit contains a cofinal omega ladder. -/
theorem exists_ladder_in_set (β : LimitBelow omegaOne) (s : Set Point)
    (hs : UnboundedBelow s β.val) :
    ∃ L : Ladder β.val, ∀ n : ℕ,
      (⟨L.seq n, (L.below n).trans β.property.1⟩ : Point) ∈ s := by
  classical
  let B := Set.Iio β.val
  letI : Countable B := countable_initialSegment (limitPoint β)
  letI : Nonempty B := ⟨⟨0, β.property.2.pos⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat B
  have hstep : ∀ b : B, ∃ d : B, b < d ∧
      (⟨d.val, d.property.trans β.property.1⟩ : Point) ∈ s := by
    intro b
    obtain ⟨d, hd, hbd, hdβ⟩ := hs b.val b.property
    exact ⟨⟨d.val, hdβ⟩, hbd, hd⟩
  choose step hgt hmem using hstep
  let a : ℕ → B := Nat.rec (step (e 0)) (fun n prev => step (max prev (e (n + 1))))
  have hea (n : ℕ) : e n < a n := by
    cases n with
    | zero => exact hgt _
    | succ n => exact (le_max_right _ _).trans_lt (hgt _)
  have ha : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact (le_max_left _ _).trans_lt (hgt _)
  refine ⟨{ seq := fun n => (a n).val
            increasing := ha
            below := fun n => (a n).property
            cofinal := ?_ }, ?_⟩
  · intro γ hγ
    obtain ⟨n, hn⟩ := he ⟨γ, hγ⟩
    exact ⟨n, by simpa only [hn] using hea n⟩
  · intro n
    cases n with
    | zero => exact hmem _
    | succ n => exact hmem _

/-- A positive ordinal supporting a strictly unbounded subset is a limit. -/
theorem isSuccLimit_of_unboundedBelow {s : Set Point} {β : Ordinal.{0}}
    (hβ : 0 < β) (hs : UnboundedBelow s β) : Order.IsSuccLimit β := by
  refine ⟨?_, Order.isSuccPrelimit_of_succ_lt ?_⟩
  · exact not_isMin_iff.mpr ⟨0, hβ⟩
  · intro γ hγ
    obtain ⟨δ, _, hγδ, hδβ⟩ := hs γ hγ
    exact (Order.succ_le_of_lt hγδ).trans_lt hδβ

/-- The nonzero accumulation points of a cofinal set. -/
def accumulationPoints (D : Set Point) : Set Point :=
  {β | 0 < β.val ∧ UnboundedBelow D β.val}

/-- Accumulation points form a club; the countable supremum remains below omega one. -/
theorem accumulationPoints_isClub (D : Set Point) (hD : IsCofinal D) :
    IsClub (accumulationPoints D) := by
  constructor
  · intro S hS hSne _ β hβ
    obtain ⟨a₀, ha₀⟩ := hSne
    refine ⟨(hS ha₀).1.trans_le (hβ.1 ha₀), ?_⟩
    intro γ hγ
    have hex : ∃ a ∈ S, γ < a.val := by
      by_contra hn
      have hupper : β ≤ (⟨γ, hγ.trans β.property⟩ : Point) := by
        apply hβ.2
        intro a ha
        exact le_of_not_gt (fun h => hn ⟨a, ha, h⟩)
      exact (not_le_of_gt hγ) hupper
    obtain ⟨a, ha, hγa⟩ := hex
    obtain ⟨δ, hδ, hγδ, hδa⟩ := (hS ha).2 γ hγa
    exact ⟨δ, hδ, hγδ, hδa.trans_le (hβ.1 ha)⟩
  · intro x
    let a : ℕ → Point := Nat.rec (nextD D hD x) (fun _ prev => nextD D hD prev)
    have ha (n : ℕ) : a n < a (n + 1) := (nextD_spec D hD (a n)).2
    have hmem (n : ℕ) : a n ∈ D := by
      cases n with
      | zero => exact (nextD_spec D hD x).1
      | succ n => exact (nextD_spec D hD (a n)).1
    let b : Ordinal.{0} := ⨆ n : ℕ, (a n).val
    have hb : b < omegaOne := Ordinal.iSup_lt_omega_one (fun n => (a n).property)
    have hab (n : ℕ) : (a n).val < b :=
      (show (a n).val < (a (n + 1)).val from ha n).trans_le (Ordinal.le_iSup (fun n => (a n).val) (n + 1))
    refine ⟨⟨b, hb⟩, ⟨?_, ?_⟩, ?_⟩
    · exact (show (0 : Ordinal) ≤ (a 0).val from bot_le).trans_lt (hab 0)
    · intro γ hγ
      obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hγ
      exact ⟨a n, hmem n, hn, hab n⟩
    · exact (nextD_spec D hD x).2.le.trans (hab 0).le

/-- Diamond, with guesses for every subset of the full first uncountable ordinal. -/
def Diamond : Prop :=
  ∃ X : Point → Set Point, (∀ β, X β ⊆ Set.Iio β) ∧
    ∀ s : Set Point, InfinitaryCombinatorics.Stationary {β | X β = s ∩ Set.Iio β}

/-- Club guessing with whole-ladder containment, rather than eventual containment. -/
def ClubGuessing : Prop :=
  ∃ C : LadderSystem, ∀ D : Set Point, IsClub D →
    ∃ β : LimitBelow omegaOne, ∀ n : ℕ, ladderPoint C β n ∈ D

/-- Lemma 7.2. Neither forcing nor constructibility is assumed in this implication. -/
theorem Diamond_implies_ClubGuessing : Diamond → ClubGuessing := by
  classical
  rintro ⟨X, _, hX⟩
  have hchoose : ∀ β : LimitBelow omegaOne, ∃ L : Ladder β.val,
      UnboundedBelow (X (limitPoint β)) β.val →
      ∀ n : ℕ, (⟨L.seq n, (L.below n).trans β.property.1⟩ : Point) ∈ X (limitPoint β) := by
    intro β
    by_cases h : UnboundedBelow (X (limitPoint β)) β.val
    · obtain ⟨L, hL⟩ := exists_ladder_in_set β (X (limitPoint β)) h
      exact ⟨L, fun _ => hL⟩
    · have huniv : UnboundedBelow Set.univ β.val := by
        intro γ hγ
        refine ⟨⟨Order.succ γ, (β.property.2.succ_lt hγ).trans β.property.1⟩,
          Set.mem_univ _, Order.lt_succ γ, β.property.2.succ_lt hγ⟩
      obtain ⟨L, _⟩ := exists_ladder_in_set β Set.univ huniv
      exact ⟨L, fun h' => False.elim (h h')⟩
  choose C hC using hchoose
  refine ⟨C, ?_⟩
  intro D hD
  obtain ⟨β, hguess, hacc⟩ := hX D (accumulationPoints D)
    (accumulationPoints_isClub D hD.isCofinal)
  let b : LimitBelow omegaOne :=
    ⟨β.val, β.property, isSuccLimit_of_unboundedBelow hacc.1 hacc.2⟩
  have hguess' : X (limitPoint b) = D ∩ Set.Iio β := hguess
  have hUb : UnboundedBelow (X (limitPoint b)) b.val := by
    intro γ hγ
    obtain ⟨δ, hδ, hγδ, hδβ⟩ := hacc.2 γ hγ
    refine ⟨δ, ?_, hγδ, hδβ⟩
    rw [hguess']
    exact ⟨hδ, hδβ⟩
  refine ⟨b, ?_⟩
  intro n
  have hmem := hC b hUb n
  rw [hguess'] at hmem
  exact hmem.1

end
end InfinitaryCombinatorics.Formalizations.A1

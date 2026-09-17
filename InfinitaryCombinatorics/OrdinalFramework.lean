import InfinitaryCombinatorics.DisjointType
import InfinitaryCombinatorics.PairColoring
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Cofinality.Club

namespace InfinitaryCombinatorics
open Set
universe u

/-- A strictly increasing omega ladder cofinal in the ordinal `α`. -/
structure Ladder (α : Ordinal.{u}) where
  seq : ℕ → Ordinal.{u}
  increasing : StrictMono seq
  below : ∀ n, seq n < α
  cofinal : ∀ β < α, ∃ n, β < seq n

namespace Ladder
variable {α : Ordinal.{u}} (C : Ladder α)

def initialSegment (n : ℕ) : Fin n → Ordinal.{u} := fun i => C.seq i.val

theorem initialSegment_strictMono (n : ℕ) : StrictMono (C.initialSegment n) :=
  fun _ _ h => C.increasing h

theorem eventually_above {β : Ordinal.{u}} (hβ : β < α) :
    ∃ N, ∀ n ≥ N, β < C.seq n := by
  obtain ⟨N, hN⟩ := C.cofinal β hβ
  exact ⟨N, fun n hn => hN.trans_le (C.increasing.monotone hn)⟩

theorem eventually_above_finite {F : Set Ordinal.{u}} (hF : F.Finite)
    (hbelow : ∀ β ∈ F, β < α) : ∃ N, ∀ n ≥ N, ∀ β ∈ F, β < C.seq n := by
  induction F, hF using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert β F hb hF ih =>
      obtain ⟨N, hN⟩ := ih (fun γ hγ => hbelow γ (mem_insert_of_mem _ hγ))
      obtain ⟨M, hM⟩ := C.eventually_above (hbelow β (mem_insert _ _))
      refine ⟨max N M, ?_⟩
      intro n hn γ hγ
      rcases mem_insert_iff.mp hγ with rfl | hγ
      · exact hM n ((le_max_right _ _).trans hn)
      · exact hN n ((le_max_left _ _).trans hn) γ hγ

theorem ordinal_ne_zero (C : Ladder α) : α ≠ 0 := ne_of_gt ((show (0 : Ordinal) ≤ C.seq 0 from bot_le).trans_lt (C.below 0))

theorem ordinal_ne_succ (C : Ladder α) (β : Ordinal.{u}) : α ≠ Order.succ β := by
  intro h
  obtain ⟨n, hn⟩ := C.cofinal β (h ▸ Order.lt_succ β)
  have hle : C.seq n ≤ β := Order.le_of_lt_succ (h ▸ C.below n)
  exact (not_lt_of_ge hle) hn

end Ladder

abbrev LimitBelow (κ : Ordinal.{u}) := {α : Ordinal.{u} // α < κ ∧ Order.IsSuccLimit α}
abbrev CSequence (κ : Ordinal.{u}) := (α : LimitBelow κ) → Ladder α.val

/-- The actual type-guessing conclusion, with positive widths `width k + 1`. -/
def TypeGuessing {κ : Ordinal.{u}} (C : CSequence κ) (width : ℕ → ℕ)
    (t : ∀ k, DisjointType (width k + 1)) : Prop :=
  ∀ f : LimitBelow κ → ℕ, ∃ α β : LimitBelow κ, ∃ k,
    α.val < β.val ∧ f α = k ∧ f β = k ∧
      ((t k).Realizes ((C α).initialSegment (width k + 1)) ((C β).initialSegment (width k + 1)) ∨
       (t k).swap.Realizes ((C α).initialSegment (width k + 1)) ((C β).initialSegment (width k + 1)))

def BoundedTypeDepth (width : ℕ → ℕ) (t : ∀ k, DisjointType (width k + 1)) : Prop :=
  ∃ d : ℕ, ∀ k, (t k).depth ≤ d

def BoundedTypeWidth (width : ℕ → ℕ) : Prop := ∃ n, ∀ k, width k + 1 ≤ n

theorem boundedDepth_of_boundedWidth {width : ℕ → ℕ}
    (t : ∀ k, DisjointType (width k + 1)) (h : BoundedTypeWidth width) :
    BoundedTypeDepth width t := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun k => (Nat.le_of_lt (t k).depth_spec.choose).trans (hn k)⟩

/-- A checked example separates the two hypotheses in A1. -/
theorem exists_boundedDepth_unboundedWidth :
    ∃ (width : ℕ → ℕ) (t : ∀ k, DisjointType (width k + 1)),
      BoundedTypeDepth width t ∧ ¬ BoundedTypeWidth width := by
  refine ⟨id, fun k => DisjointType.separated (k + 1), ?_, ?_⟩
  · exact ⟨0, fun k => by simp [DisjointType.separated_depth]⟩
  · rintro ⟨n, hn⟩
    have h := hn n
    change n + 1 ≤ n at h
    omega

/-- Stationarity relative to the existing mathlib notion of club. -/
def Stationary {α : Type*} [LinearOrder α] (S : Set α) : Prop :=
  ∀ C : Set α, IsClub C → (S ∩ C).Nonempty

theorem Stationary.mono {α : Type*} [LinearOrder α] {S T : Set α}
    (hS : Stationary S) (hST : S ⊆ T) : Stationary T := by
  intro C hC
  obtain ⟨x, hx, hxc⟩ := hS C hC
  exact ⟨x, hST hx, hxc⟩

theorem Stationary.inter_club {α : Type*} [LinearOrder α] [WellFoundedLT α]
    {S C : Set α} (hS : Stationary S) (hC : IsClub C) (hα : Order.cof α ≠ Cardinal.aleph0) :
    Stationary (S ∩ C) := by
  intro D hD
  obtain ⟨x, hx, hxc, hxd⟩ := hS (C ∩ D) (hC.inter hα hD)
  exact ⟨x, ⟨hx, hxc⟩, hxd⟩

/-- Lower neighbours, written in the ambient ordinal rather than the vertex subtype. -/
def lowerNeighbors {κ : Ordinal.{u}} (G : SimpleGraph (Set.Iio κ)) (α : Set.Iio κ) :
    Set Ordinal.{u} := {β | ∃ hβ : β < κ, β < α.val ∧ G.Adj ⟨β, hβ⟩ α}

def LadderLike {κ : Ordinal.{u}} (G : SimpleGraph (Set.Iio κ)) : Prop :=
  ∀ α, (lowerNeighbors G α).Finite ∨
    ∃ C : Ladder α.val, lowerNeighbors G α = Set.range C.seq

/-- Uncountable chromaticity is stated via absence of a Nat-valued proper coloring. -/
def HajnalMate {κ : Ordinal.{u}} (G : SimpleGraph (Set.Iio κ)) : Prop :=
  LadderLike G ∧ ¬ Nonempty (G.Coloring ℕ)

def RegressiveUncolorable {κ : Ordinal.{u}} (G : SimpleGraph (Set.Iio κ)) : Prop :=
  ¬ ∃ c : G.Coloring (Set.Iio κ), ∀ α, Order.IsSuccLimit α.val → (c α).val < α.val

end InfinitaryCombinatorics





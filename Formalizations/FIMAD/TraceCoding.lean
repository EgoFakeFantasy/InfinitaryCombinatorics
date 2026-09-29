import InfinitaryCombinatorics.FinIntersection
import Mathlib.Data.Finset.Max

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set

/-- Eventual domination, with a separate threshold for each function. -/
def EventuallyLE (f g : ℕ → ℕ) : Prop := ∃ N, ∀ n ≥ N, f n ≤ g n

/-- Every family of functions indexed by U has a common eventual bound. -/
def Bounding (U : Set (Set ℕ)) : Prop :=
  ∀ f : U → ℕ → ℕ, ∃ g : ℕ → ℕ, ∀ a, EventuallyLE (f a) g

/-- Equality of sets outside a finite initial interval. -/
def EventuallyEqual (s t : Set ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, n ∈ s ↔ n ∈ t

lemma infinite_tail_point {s : Set ℕ} (hs : s.Infinite) (k : ℕ) :
    ∃ x ∈ s, k ≤ x := by
  by_contra h
  push Not at h
  exact hs ((finite_lt_nat k).subset (fun x hx => h x hx))

/-- Paper Lemma 3.1. No almost-disjointness hypothesis is needed. -/
theorem uniform_trace_coding (U : Set (Set ℕ)) (hb : Bounding U)
    (S : U → Set ℕ) (X : ℕ → Set ℕ) (hX : ∀ n, (X n).Infinite)
    (ht : ∀ a : U, ∀ n, ((a : Set ℕ) ∩ X n).Infinite ↔ n ∈ S a) :
    ∃ C : R0.FinSequence ℕ, ∀ a : U, EventuallyEqual (R0.trace C a) (S a) := by
  classical
  have hd : ∀ a : U, ∀ k, ∃ d, k ∉ S a → ∀ x ∈ (a : Set ℕ) ∩ X k, x < d := by
    intro a k
    by_cases hk : k ∈ S a
    · exact ⟨0, fun h => (h hk).elim⟩
    · have hf : ((a : Set ℕ) ∩ X k).Finite := not_infinite.mp (mt (ht a k).mp hk)
      obtain ⟨d, hbd⟩ := hf.bddAbove
      exact ⟨d+1, fun _ x hx => Nat.lt_succ_of_le (hbd hx)⟩
  choose d hd using hd
  have hp : ∀ a : U, ∀ k i, ∃ p, i ∈ S a → p ∈ (a : Set ℕ) ∩ X i ∧ k ≤ p := by
    intro a k i
    by_cases hi : i ∈ S a
    · obtain ⟨p,hp,hkp⟩ := infinite_tail_point ((ht a i).mpr hi) k
      exact ⟨p,fun _ => ⟨hp,hkp⟩⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose p hp using hp
  let f : U → ℕ → ℕ := fun a k => max (d a k) ((Finset.range (k+1)).sup (p a k))
  obtain ⟨g,hg⟩ := hb f
  let r : ℕ → ℕ := fun n => Nat.rec 0 (fun n r =>
    let l := max n (max (g n) r)
    let z := Classical.choose (infinite_tail_point (hX n) l)
    1 + max l (max (g l) z)) n
  let l : ℕ → ℕ := fun n => max n (max (g n) (r n))
  let z : ℕ → ℕ := fun n => Classical.choose (infinite_tail_point (hX n) (l n))
  have hr (n) : r (n+1) = 1 + max (l n) (max (g (l n)) (z n)) := rfl
  have hnl (n) : n ≤ l n := le_max_left _ _
  have hgl (n) : g n ≤ l n := (le_max_left _ _).trans (le_max_right _ _)
  have hrl (n) : r n ≤ l n := (le_max_right _ _).trans (le_max_right _ _)
  have hlr (n) : l n < r (n+1) := by rw [hr]; omega
  have hgr (n) : g (l n) < r (n+1) := by rw [hr]; omega
  have hzr (n) : z n < r (n+1) := by rw [hr]; omega
  have hz (n) : z n ∈ X n ∧ l n ≤ z n :=
    Classical.choose_spec (infinite_tail_point (hX n) (l n))
  have hrmono : Monotone r := (strictMono_nat_of_lt_succ (fun n => (hrl n).trans_lt (hlr n))).monotone
  let C : R0.FinSequence ℕ := {
    block := fun n => {x | x ∈ X n ∧ l n ≤ x ∧ x < r (n+1)}
    finite := fun n => (finite_lt_nat (r (n+1))).subset (fun _ hx => hx.2.2)
    nonempty := fun n => ⟨z n, (hz n).1, (hz n).2, hzr n⟩
    disjoint := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      intro x hx hy
      change x ∈ X n ∧ l n ≤ x ∧ x < r (n+1) at hx
      change x ∈ X m ∧ l m ≤ x ∧ x < r (m+1) at hy
      rcases lt_or_gt_of_ne hnm with h | h
      · have hsep : r (n+1) ≤ l m := (hrmono (Nat.succ_le_of_lt h)).trans (hrl m)
        exact (not_lt_of_ge (hsep.trans hy.2.1)) hx.2.2
      · have hsep : r (m+1) ≤ l n := (hrmono (Nat.succ_le_of_lt h)).trans (hrl n)
        exact (not_lt_of_ge (hsep.trans hx.2.1)) hy.2.2 }
  refine ⟨C, ?_⟩
  intro a
  obtain ⟨N,hN⟩ := hg a
  refine ⟨N, ?_⟩
  intro n hn
  constructor
  · rintro ⟨x,hxa,hx⟩
    by_contra hnot
    have hneg := hd a n hnot x ⟨hxa,hx.1⟩
    have hdn : d a n ≤ g n := (le_max_left _ _).trans (hN n hn)
    have := hgl n
    change x ∈ X n ∧ l n ≤ x ∧ x < r (n+1) at hx
    omega
  · intro hpos
    have hpl : p a (l n) n ≤ f a (l n) := by
      apply (Finset.le_sup (s := Finset.range (l n+1)) (f := p a (l n)) ?_).trans (le_max_right _ _)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hnl n))
    have hbound := hN (l n) (hn.trans (hnl n))
    have hpoint := hp a (l n) n hpos
    refine ⟨p a (l n) n, hpoint.1.1, hpoint.1.2, hpoint.2, ?_⟩
    exact (hpl.trans hbound).trans_lt (hgr n)

end InfinitaryCombinatorics.Formalizations.FIMAD

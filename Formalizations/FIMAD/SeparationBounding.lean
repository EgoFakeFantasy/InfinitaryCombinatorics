import Formalizations.FIMAD.Obstruction
import Formalizations.R0.UniformMAD
import Mathlib.Order.Iterate

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal
open _root_.R0 (Node node wordPrefix node_injective nodeEquivNat)
open InfinitaryCombinatorics.Formalizations.R0 (branch branch_infinite branch_inter_finite branch_injective)

lemma countable_functions_bounded {F : Set (ℕ → ℕ)} (hF : F.Countable) :
    ∃ g, ∀ f ∈ F, EventuallyLE f g := by
  classical
  obtain ⟨e, he⟩ := countable_iff_exists_subset_range.mp hF
  refine ⟨fun n => (Finset.range (n + 1)).sup (fun i => e i n), ?_⟩
  intro f hf
  obtain ⟨i, rfl⟩ := he hf
  exact ⟨i, fun n hn => Finset.le_sup (f := fun j => e j n) (Finset.mem_range.mpr (by omega))⟩

lemma aleph0_lt_boundingNumber : ℵ₀ < boundingNumber := by
  obtain ⟨F, hF, hc⟩ := csInf_mem unboundedCardinals_nonempty
  change ℵ₀ < sInf unboundedCardinals
  rw [← hc]
  by_contra hn
  exact hF (countable_functions_bounded (Cardinal.le_aleph0_iff_set_countable.mp (le_of_not_gt hn)))

/-- A monotone envelope whose diagonal iterates absorb every eventually
bounded recurrence, regardless of its starting point. -/
lemma recurrence_eventually_bounded (H : ℕ → ℕ) (hH : Monotone H)
    (hid : ∀ n, n ≤ H n) {p : ℕ → ℕ}
    (hp : ∃ N, ∀ n ≥ N, p (n + 1) ≤ H (p n)) :
    EventuallyLE p (fun n => H^[n] n) := by
  obtain ⟨N, hN⟩ := hp
  have hb (k) : p (N + k) ≤ H^[k] (p N) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (hN (N + k) (by omega)).trans (hH ih)
  refine ⟨max N (p N), ?_⟩
  intro n hn
  have hNn : N ≤ n := (le_max_left _ _).trans hn
  calc
    p n = p (N + (n - N)) := by congr 1; omega
    _ ≤ H^[n - N] (p N) := hb _
    _ ≤ H^[n - N] n := hH.iterate _ ((le_max_right _ _).trans hn)
    _ ≤ H^[n] n := Function.monotone_iterate_of_id_le hid (Nat.sub_le _ _) n

/-- Every function is pointwise below an increasing enumeration. -/
def increasingEnvelope (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => max (increasingEnvelope f n + 1) (f (n + 1))

lemma increasingEnvelope_strictMono (f : ℕ → ℕ) : StrictMono (increasingEnvelope f) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

lemma le_increasingEnvelope (f : ℕ → ℕ) (n : ℕ) : f n ≤ increasingEnvelope f n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

lemma node_eq_of_agree {s t : Set ℕ} {m : ℕ}
    (h : ∀ k < m, k ∈ s ↔ k ∈ t) : node s m = node t m := by
  change (m, wordPrefix s m) = (m, wordPrefix t m)
  congr 1
  ext k
  simp only [wordPrefix, Finset.mem_filter, Finset.mem_range]
  exact and_congr_right (h k)

/-- A set of tree nodes meeting every eventually-zero branch infinitely
often bounds the increasing enumerations of all branches it meets finitely. -/
lemma finite_branch_intersections_bounded (X : Set Node)
    (hX : ∀ t : Finset ℕ, (branch (t : Set ℕ) ∩ X).Infinite) :
    ∃ g : ℕ → ℕ, ∀ p : ℕ → ℕ, StrictMono p →
      (branch (range p) ∩ X).Finite → EventuallyLE p g := by
  classical
  have hw (t : Finset ℕ) (k : ℕ) : ∃ m ≥ k, node (t : Set ℕ) m ∈ X := by
    have hi : {m | node (t : Set ℕ) m ∈ X}.Infinite := by
      intro hf
      apply hX t
      apply (hf.image (node (t : Set ℕ))).subset
      rintro x ⟨⟨m, rfl⟩, hm⟩
      exact ⟨m, hm, rfl⟩
    obtain ⟨m, hm, hk⟩ := infinite_tail_point hi k
    exact ⟨m, hk, hm⟩
  choose w hw hwX using hw
  let H : ℕ → ℕ := fun k => max k
    ((Finset.range (k + 1)).sup fun j =>
      ((Finset.range (j + 1)).powerset).sup fun t => w t (j + 1))
  have hH : Monotone H := by
    intro k l hkl
    apply max_le_max hkl
    apply Finset.sup_mono
    exact Finset.range_mono (by omega)
  have hid (k) : k ≤ H k := le_max_left _ _
  refine ⟨fun n => H^[n] n, ?_⟩
  intro p hp hf
  have hpre : {m | node (range p) m ∈ X}.Finite := by
    apply (hf.preimage (node_injective (range p)).injOn).subset
    intro m hm
    exact ⟨mem_range_self m, hm⟩
  obtain ⟨N, hN⟩ := hpre.bddAbove
  apply recurrence_eventually_bounded H hH hid
  refine ⟨N + 1, ?_⟩
  intro n hn
  let t := wordPrefix (range p) (p n + 1)
  have ht : t ⊆ Finset.range (p n + 1) := Finset.filter_subset _ _
  have hmH : w t (p n + 1) ≤ H (p n) := by
    apply le_trans _ (le_max_right _ _)
    apply le_trans (Finset.le_sup (f := fun t => w t (p n + 1)) (Finset.mem_powerset.mpr ht))
    exact Finset.le_sup (f := fun j => ((Finset.range (j + 1)).powerset).sup fun t => w t (j + 1))
      (Finset.mem_range.mpr (Nat.lt_succ_self _))
  by_contra hnot
  have hmp : w t (p n + 1) ≤ p (n + 1) := by omega
  have heq : node (range p) (w t (p n + 1)) = node (t : Set ℕ) (w t (p n + 1)) := by
    apply node_eq_of_agree
    intro k hk
    simp only [t, wordPrefix, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      have hi : i ≤ n := by
        by_contra hi
        have := hp.monotone (show n + 1 ≤ i by omega)
        omega
      exact ⟨Nat.lt_succ_of_le (hp.monotone hi), mem_range_self _⟩
    · exact fun h => h.2
  have hmX : node (range p) (w t (p n + 1)) ∈ X := heq ▸ hwX t (p n + 1)
  have hsmall : w t (p n + 1) ≤ N := hN hmX
  have hlarge := hw t (p n + 1)
  have hnp : n ≤ p n := hp.id_le n
  omega

/-- The comparison ap ≤ b, proved directly with branches of the binary tree. -/
theorem almostDisjointSeparationNumber_le_boundingNumber :
    almostDisjointSeparationNumber ≤ boundingNumber := by
  classical
  by_contra hnot
  have hlt : boundingNumber < almostDisjointSeparationNumber := lt_of_not_ge hnot
  obtain ⟨F, hF, hc⟩ := csInf_mem unboundedCardinals_nonempty
  change #F = boundingNumber at hc
  let Q : Set (Set ℕ) := range (fun t : Finset ℕ => (t : Set ℕ))
  let P : Set (Set ℕ) := range (fun f : F => range (increasingEnvelope f.val))
  let T := Q ∪ P
  let e := nodeEquivNat
  let B : Set ℕ → Set ℕ := fun s => e '' branch s
  have hBi : Function.Injective B := by
    intro s t h
    exact branch_injective (e.injective.image_injective h)
  let A := B '' T
  have hAD : ADFamily A := by
    constructor
    · rintro a ⟨s, hs, rfl⟩
      exact (branch_infinite s).image e.injective.injOn
    · rintro a ⟨s, hs, rfl⟩ b ⟨t, ht, rfl⟩ hne
      change (e '' branch s ∩ e '' branch t).Finite
      rw [← Set.image_inter e.injective]
      exact (branch_inter_finite (show s ≠ t from fun h => hne (congrArg B h))).image e
  have hcard : #A < almostDisjointSeparationNumber := by
    apply lt_of_le_of_lt _ hlt
    calc
      #A ≤ #T := Cardinal.mk_image_le
      _ ≤ #Q + #P := Cardinal.mk_union_le _ _
      _ ≤ ℵ₀ + #F := add_le_add (countable_range _).le_aleph0 Cardinal.mk_range_le
      _ = boundingNumber := by rw [hc, Cardinal.add_eq_right aleph0_lt_boundingNumber.le aleph0_lt_boundingNumber.le]
  obtain ⟨Y, hY⟩ := weaklySeparable_of_card_lt hAD hcard (B '' Q)
    (Set.image_mono (subset_union_left))
  let X := e ⁻¹' Y
  have hXY (s : Set ℕ) : (branch s ∩ X).Infinite ↔ (B s ∩ Y).Infinite := by
    have heq : e '' (branch s ∩ X) = B s ∩ Y := by
      ext x
      constructor
      · rintro ⟨z, ⟨hz, hy⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, hy⟩
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        exact ⟨z, ⟨hz, hy⟩, rfl⟩
    rw [← heq]
    exact (Set.infinite_image_iff e.injective.injOn).symm
  have hpos (t : Finset ℕ) : (branch (t : Set ℕ) ∩ X).Infinite := by
    apply (hXY _).mpr
    apply (hY _ ⟨_, Or.inl (mem_range_self t), rfl⟩).mpr
    exact ⟨_, mem_range_self t, rfl⟩
  obtain ⟨g, hg⟩ := finite_branch_intersections_bounded X hpos
  apply hF
  refine ⟨g, ?_⟩
  intro f hf
  let p := increasingEnvelope f
  have hp := increasingEnvelope_strictMono f
  have hneg : (branch (range p) ∩ X).Finite := by
    apply Set.not_infinite.mp
    intro hi
    have hmem := (hY _ ⟨_, Or.inr (mem_range_self (⟨f, hf⟩ : F)), rfl⟩).mp ((hXY _).mp hi)
    obtain ⟨s, ⟨t, rfl⟩, heq⟩ := hmem
    have hsets : (t : Set ℕ) = range p := hBi heq
    exact (infinite_range_of_injective hp.injective) (hsets ▸ t.finite_toSet)
  obtain ⟨N, hN⟩ := hg p hp hneg
  exact ⟨N, fun n hn => (le_increasingEnvelope f n).trans (hN n hn)⟩

end InfinitaryCombinatorics.Formalizations.FIMAD

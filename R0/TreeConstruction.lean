import R0.Basic

namespace R0
open Set

/-- A binary word is represented by its length and the finite set of its one-bits.
The ambient countable type also contains unused pairs; every block below consists
exactly of the valid words of its stated length. -/
abbrev Node := ℕ × Finset ℕ

noncomputable def wordPrefix (s : Set ℕ) (n : ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun k => k ∈ s) (Classical.decPred _) (Finset.range n)

noncomputable def node (s : Set ℕ) (n : ℕ) : Node := (n, wordPrefix s n)

lemma node_injective (s : Set ℕ) : Function.Injective (node s) := by
  intro n m h
  exact congrArg Prod.fst h

def indices (s : Set ℕ) (b : Bool) : Set ℕ := if b then sᶜ else s

noncomputable def half (s : Set ℕ) (b : Bool) : Set Node := node s '' indices s b

def level (n : ℕ) : Set Node :=
  (fun a : Finset ℕ => (n, a)) '' (↑(Finset.range n).powerset : Set (Finset ℕ))

def treeBlocks : FinSequence Node where
  block := level
  finite n := (Finset.finite_toSet _).image _
  nonempty n := ⟨(n, ∅), ∅, by simp, rfl⟩
  disjoint n m hnm := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, _, rfl⟩ ⟨b, _, heq⟩
    exact hnm (congrArg Prod.fst heq).symm

lemma node_mem_level (s : Set ℕ) (n : ℕ) : node s n ∈ level n := by
  classical
  refine ⟨wordPrefix s n, ?_, rfl⟩
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)

lemma trace_half (s : Set ℕ) (b : Bool) : trace treeBlocks (half s b) = indices s b := by
  ext n
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, a, _, heq⟩
    have hkn : k = n := (congrArg Prod.fst heq).symm
    simpa [hkn] using hk
  · intro hn
    exact ⟨node s n, ⟨n, hn, rfl⟩, node_mem_level s n⟩

lemma half_infinite {s : Set ℕ} (hs : s.Infinite) (hsc : sᶜ.Infinite) (b : Bool) :
    (half s b).Infinite := by
  cases b with
  | false => exact Set.Infinite.image (node_injective s).injOn hs
  | true => exact Set.Infinite.image (node_injective s).injOn hsc

lemma half_inter_same (s : Set ℕ) {b c : Bool} (hbc : b ≠ c) :
    (half s b ∩ half s c).Finite := by
  cases b <;> cases c <;>
    simp_all [half, indices, ← Set.image_inter (node_injective s)]

lemma half_inter_of_ne {s t : Set ℕ} (hst : s ≠ t) (b c : Bool) :
    (half s b ∩ half t c).Finite := by
  classical
  have hex : ∃ k, ¬ (k ∈ s ↔ k ∈ t) := by
    by_contra h
    push Not at h
    exact hst (Set.ext h)
  obtain ⟨k, hk⟩ := hex
  apply ((Finset.range (k + 1)).finite_toSet.image (node s)).subset
  rintro z ⟨⟨n, hn, hzn⟩, m, hm, hzm⟩
  have hnm : n = m := congrArg Prod.fst (hzn.trans hzm.symm)
  subst m
  have hle : n ≤ k := by
    by_contra h
    have hkn : k < n := by omega
    have hp : wordPrefix s n = wordPrefix t n := congrArg Prod.snd (hzn.trans hzm.symm)
    have hmem : k ∈ wordPrefix s n ↔ k ∈ wordPrefix t n := by rw [hp]
    exact hk (by simpa [wordPrefix, hkn] using hmem)
  exact ⟨n, Finset.mem_range.mpr (by omega), hzn⟩

noncomputable def treeFamily (S : Set (Set ℕ)) : Set (Set Node) :=
  Set.range fun p : S × Bool => half p.1.val p.2

lemma not_centered_of_disjoint {T : Set (Set ℕ)} {t u : Set ℕ}
    (ht : t ∈ T) (hu : u ∈ T) (hdisj : t ∩ u = ∅) : ¬ Centered T := by
  intro hC
  have hsub : ({t, u} : Set (Set ℕ)) ⊆ T := by
    intro a ha
    rcases mem_insert_iff.mp ha with rfl | ha
    · exact ht
    · exact mem_singleton_iff.mp ha ▸ hu
  have h := hC {t, u} hsub (by simp) (by simp)
  have hinf : (t ∩ u).Infinite := by simpa using h
  exact hinf (hdisj ▸ finite_empty)

/-- The blocks are fixed before the infinite set of indices is chosen. -/
theorem treeFamily_not_finIntersecting {S : Set (Set ℕ)} (hS : Splitting S) :
    ¬ FinIntersecting (treeFamily S) := by
  intro hFI
  obtain ⟨i, hi, hc⟩ := hFI treeBlocks
  obtain ⟨s, hs, h0, h1⟩ := hS i hi
  have hmem (b : Bool) : half s b ∈ treeFamily S :=
    ⟨(⟨s, hs⟩, b), rfl⟩
  have ht0 : i ∩ s ∈ retainedTraces treeBlocks (treeFamily S) i := by
    refine ⟨h0, half s false, hmem false, ?_⟩
    rw [trace_half]
    rfl
  have ht1 : i \ s ∈ retainedTraces treeBlocks (treeFamily S) i := by
    refine ⟨h1, half s true, hmem true, ?_⟩
    rw [trace_half]
    rfl
  have hdisj : (i ∩ s) ∩ (i \ s) = ∅ := by
    ext n
    constructor
    · intro hn; exact hn.2.2 hn.1.2
    · intro hn; exact hn.elim
  exact not_centered_of_disjoint ht0 ht1 hdisj hc

end R0

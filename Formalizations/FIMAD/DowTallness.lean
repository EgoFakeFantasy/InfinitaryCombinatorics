import Formalizations.FIMAD.DowPossibleValues

/-! Countable witnesses for Dow forcing's tallness preservation, stated with
explicit monotone dense decision relations. This is the single-poset
combinatorial argument; no forcing-name semantics or iteration is assumed. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
open Set
variable {A : Set (Set ℕ)}

def valueTail (E : ℕ → Condition A → ℕ → Prop) (s : Finset ℕ) (N : ℕ) : Set ℕ :=
  {k | ∃ i, N ≤ i ∧ k ∈ Possible (E i) s}

/-- Any increasing enumeration-name decision relation has countable ground
tests which make hitting B dense at arbitrarily large indices. The three
premises are precise properties of that relation, not preservation premises. -/
theorem countable_tallness_tests (E : ℕ → Condition A → ℕ → Prop)
    (hmono : ∀ i p q, q ≤ p → ∀ k, E i p k → E i q k)
    (hdec : ∀ i, Dense {p | ∃ k, E i p k})
    (hlower : ∀ i p k, E i p k → i ≤ k) :
    ∃ F : Set (Set ℕ), F.Countable ∧ (∀ X ∈ F, X.Infinite) ∧
      ∀ B, (∀ X ∈ F, (X ∩ B).Infinite) →
        ∀ p N, ∃ q, q ≤ p ∧ ∃ i, N ≤ i ∧ ∃ k ∈ B, E i q k := by
  classical
  have htests (i : ℕ) (s : Finset ℕ) :
      ∃ F : Set (Set ℕ), F.Countable ∧ ∀ B, MeetsTests B F →
        ∀ p : Condition A, p.stem = s → Avoids (E i) p B → (Possible (E i) s).Nonempty :=
    reach_possible_tests (hmono i) (fun _ h => h) (reach_all (hdec i) s)
  choose F hF hgood using htests
  let H : Set (Set ℕ) := (⋃ i, ⋃ s, F i s) ∪
    range (fun j : Finset ℕ × ℕ => valueTail E j.1 j.2)
  have hH : H.Countable := (countable_iUnion (fun i => countable_iUnion (hF i))).union
    (countable_range _)
  refine ⟨{X ∈ H | X.Infinite}, hH.mono (fun _ h => h.1), fun _ h => h.2, ?_⟩
  intro B hB p N
  by_contra hnone
  have hav (i) (hi : N ≤ i) : Avoids (E i) p B := by
    intro q hq k hk he
    exact hnone ⟨q, hq, i, hi, k, hk, he⟩
  have hne (i) (hi : N ≤ i) : (Possible (E i) p.stem).Nonempty := by
    apply hgood i p.stem B ?_ p rfl (hav i hi)
    intro X hX hXi
    exact hB X ⟨Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨p.stem, hX⟩⟩), hXi⟩
  have hlarge (i) (k) (hk : k ∈ Possible (E i) p.stem) : i ≤ k := by
    obtain ⟨q, _, hq⟩ := hk p rfl
    exact hlower i q k hq
  have hi : (valueTail E p.stem N).Infinite := by
    intro hf
    obtain ⟨m, hm⟩ := hf.bddAbove
    obtain ⟨k, hk⟩ := hne (max N (m + 1)) (le_max_left _ _)
    have hkU : k ∈ valueTail E p.stem N := ⟨max N (m + 1), le_max_left _ _, hk⟩
    exact (Nat.not_succ_le_self m) ((le_max_right N (m + 1)).trans
      ((hlarge _ k hk).trans (hm hkU)))
  obtain ⟨k, hk, hkB⟩ := (hB _ ⟨Or.inr (mem_range_self (p.stem, N)), hi⟩).nonempty
  obtain ⟨i, hi, hki⟩ := hk
  obtain ⟨q, hq, he⟩ := hki p rfl
  exact hnone ⟨q, hq, i, hi, k, hkB, he⟩

/-- One countable test family works for countably many enumeration names. -/
theorem simultaneous_tallness_tests (E : ℕ → ℕ → Condition A → ℕ → Prop)
    (hmono : ∀ j i p q, q ≤ p → ∀ k, E j i p k → E j i q k)
    (hdec : ∀ j i, Dense {p | ∃ k, E j i p k})
    (hlower : ∀ j i p k, E j i p k → i ≤ k) :
    ∃ F : Set (Set ℕ), F.Countable ∧ (∀ X ∈ F, X.Infinite) ∧
      ∀ B, (∀ X ∈ F, (X ∩ B).Infinite) →
        ∀ j p N, ∃ q, q ≤ p ∧ ∃ i, N ≤ i ∧ ∃ k ∈ B, E j i q k := by
  choose F hF hFi hgood using fun j => countable_tallness_tests (E j) (hmono j) (hdec j) (hlower j)
  refine ⟨⋃ j, F j, countable_iUnion hF, ?_, ?_⟩
  · intro X hX
    obtain ⟨j, hj⟩ := mem_iUnion.mp hX
    exact hFi j X hj
  · intro B hB j
    exact hgood j B (fun X hX => hB X (mem_iUnion.mpr ⟨j, hX⟩))

/-- The same tests control both sides of splitting, for every member of a
countable collection of names. Membership decisions on each side are dense. -/
theorem simultaneous_splitting_tests (E : ℕ → ℕ → Condition A → ℕ → Prop)
    (hmono : ∀ j i p q, q ≤ p → ∀ k, E j i p k → E j i q k)
    (hdec : ∀ j i, Dense {p | ∃ k, E j i p k})
    (hlower : ∀ j i p k, E j i p k → i ≤ k) :
    ∃ F : Set (Set ℕ), F.Countable ∧ (∀ X ∈ F, X.Infinite) ∧
      ∀ B, (∀ X ∈ F, R0.Splits B X) → ∀ j N,
        Dense {q | ∃ i, N ≤ i ∧ ∃ k ∈ B, E j i q k} ∧
        Dense {q | ∃ i, N ≤ i ∧ ∃ k ∉ B, E j i q k} := by
  obtain ⟨F, hF, hFi, hgood⟩ := simultaneous_tallness_tests E hmono hdec hlower
  refine ⟨F, hF, hFi, fun B hB j N => ⟨?_, ?_⟩⟩
  · intro p
    obtain ⟨q, hq, hval⟩ := hgood B (fun X hX => (hB X hX).1) j p N
    exact ⟨q, hval, hq⟩
  · intro p
    obtain ⟨q, hq, hval⟩ := hgood Bᶜ (fun X hX => (hB X hX).2) j p N
    exact ⟨q, hval, hq⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing

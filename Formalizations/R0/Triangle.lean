import Formalizations.R0.Selectors

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

noncomputable def triangleValue (s : Set ℕ) (n : ℕ) := prefixValue s (Nat.log 2 (n + 1))

lemma triangleValue_le (s : Set ℕ) (n : ℕ) : triangleValue s n ≤ n := by
  have h := (prefixValue_lt s (Nat.log 2 (n + 1))).trans_le
    (Nat.pow_log_le_self 2 (by omega : n + 1 ≠ 0))
  exact Nat.le_of_lt_succ h

lemma triangleValue_eventually_ne {s t : Set ℕ} (hst : s ≠ t) :
    ∃ N, ∀ n, N ≤ n → triangleValue s n ≠ triangleValue t n := by
  obtain ⟨L, hL⟩ := prefixValue_eventually_ne hst
  refine ⟨2 ^ L, fun n hn => hL _ ?_⟩
  exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)

abbrev Triangle := {p : ℕ × ℕ // p.2 ≤ p.1}

def triangleRow (n : ℕ) : Set Triangle :=
  range (fun m : Fin (n + 1) => ⟨(n, m.val), Nat.le_of_lt_succ m.isLt⟩)

def triangleRows : FinSequence Triangle where
  block := triangleRow
  finite n := Set.finite_range _
  nonempty n := ⟨⟨(n, 0), Nat.zero_le n⟩, ⟨0, by omega⟩, rfl⟩
  disjoint n m hnm := by
    apply Set.disjoint_left.mpr
    rintro x ⟨i, rfl⟩ ⟨j, hj⟩
    exact hnm (congrArg (fun p : Triangle => p.val.1) hj).symm

noncomputable def triangleSelector (s : Set ℕ) (n : ℕ) : Triangle :=
  ⟨(n, triangleValue s n), triangleValue_le s n⟩

lemma triangleSelector_mem (s : Set ℕ) (n : ℕ) : triangleSelector s n ∈ triangleRows.block n :=
  ⟨⟨triangleValue s n, Nat.lt_succ_of_le (triangleValue_le s n)⟩, rfl⟩

lemma triangleSelector_eventually_ne {s t : Set ℕ} (hst : s ≠ t) :
    ∃ N, ∀ n, N ≤ n → triangleSelector s n ≠ triangleSelector t n := by
  obtain ⟨N, hN⟩ := triangleValue_eventually_ne hst
  exact ⟨N, fun n hn heq => hN n hn (congrArg (fun p : Triangle => p.val.2) heq)⟩

noncomputable def triangleHalf (s : Set ℕ) (b : Bool) := triangleSelector s '' indices s b
noncomputable def triangleFamily (S : Set (Set ℕ)) := range (fun p : S × Bool => triangleHalf p.1.val p.2)

lemma triangleHalf_trace (s : Set ℕ) (b : Bool) :
    trace triangleRows (triangleHalf s b) = indices s b :=
  selector_trace triangleRows triangleSelector triangleSelector_mem _ _

lemma triangleHalf_infinite {s : Set ℕ} (hs : s.Infinite) (hsc : sᶜ.Infinite) (b : Bool) :
    (triangleHalf s b).Infinite := by
  have hinj := selector_injective triangleRows triangleSelector triangleSelector_mem s
  cases b with
  | false => exact hs.image hinj.injOn
  | true => exact hsc.image hinj.injOn

lemma triangleHalf_inter_same (s : Set ℕ) {b c : Bool} (hbc : b ≠ c) :
    (triangleHalf s b ∩ triangleHalf s c).Finite := by
  have hinj := selector_injective triangleRows triangleSelector triangleSelector_mem s
  cases b <;> cases c <;> simp_all [triangleHalf, indices, ← Set.image_inter hinj]

lemma triangleHalf_inter_ne {s t : Set ℕ} (hst : s ≠ t) (b c : Bool) :
    (triangleHalf s b ∩ triangleHalf t c).Finite :=
  selector_inter_finite triangleRows triangleSelector triangleSelector_mem
    (triangleSelector_eventually_ne hst) _ _

lemma triangleFamily_not_finIntersecting {S : Set (Set ℕ)} (hS : Splitting S) :
    ¬ FinIntersecting (triangleFamily S) := by
  apply not_finIntersecting_of_split_traces _ triangleRows
  intro I hI
  obtain ⟨s, hs, h0, h1⟩ := hS I hI
  refine ⟨triangleHalf s false, ⟨(⟨s, hs⟩, false), rfl⟩,
    triangleHalf s true, ⟨(⟨s, hs⟩, true), rfl⟩, ?_⟩
  rw [triangleHalf_trace, triangleHalf_trace]
  exact ⟨h0, h1, Set.disjoint_left.mpr (fun _ hn hm => hm.2 hn.2)⟩

lemma triangleFamily_card {S : Set (Set ℕ)} (hS : Splitting S)
    (hreg : ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite) : #(triangleFamily S) = #S := by
  apply le_antisymm
  · letI := hS.infinite.to_subtype
    calc
      #(triangleFamily S) ≤ #(S × Bool) := Cardinal.mk_range_le
      _ = #S * 2 := by simp
      _ = #S := Cardinal.mul_eq_left (Cardinal.aleph0_le_mk S)
        ((Cardinal.natCast_le_aleph0 (n := 2)).trans (Cardinal.aleph0_le_mk S)) (by simp)
  · let f : S → triangleFamily S := fun s => ⟨triangleHalf s.val false, ⟨(s, false), rfl⟩⟩
    apply Cardinal.mk_le_of_injective (f := f)
    intro s t heq
    apply Subtype.ext
    by_contra hst
    have hf := triangleHalf_inter_ne hst false false
    have hv : triangleHalf s.val false = triangleHalf t.val false := congrArg Subtype.val heq
    rw [hv, inter_self] at hf
    exact triangleHalf_infinite (hreg t.val t.property).1 (hreg t.val t.property).2 false hf

lemma triangleFamily_almostDisjoint {S : Set (Set ℕ)} (hS : Splitting S)
    (hreg : ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite) : AlmostDisjoint (triangleFamily S) := by
  have hc := triangleFamily_card hS hreg
  have hω : ℵ₀ ≤ #S := by
    letI := hS.infinite.to_subtype
    exact Cardinal.aleph0_le_mk S
  have hi : (triangleFamily S).Infinite := Set.infinite_coe_iff.mp
    (Cardinal.aleph0_le_mk_iff.mp (hc.symm ▸ hω))
  refine ⟨hi, ?_, ?_⟩
  · rintro a ⟨⟨s, b⟩, rfl⟩
    exact triangleHalf_infinite (hreg s.val s.property).1 (hreg s.val s.property).2 b
  · rintro a ⟨⟨s, b⟩, rfl⟩ d ⟨⟨t, c⟩, rfl⟩ had
    by_cases hst : s = t
    · subst t
      exact triangleHalf_inter_same s.val (fun hbc => had (congrArg (triangleHalf s.val) hbc))
    · exact triangleHalf_inter_ne (fun heq => hst (Subtype.ext heq)) b c

/-- Appendix A on its precise triangular ground set, with the explicit
logarithmic prefix function, row traces and the original cardinality. -/
theorem triangle_counterexample :
    ∃ S : Set (Set ℕ), Splitting S ∧ #S = splittingNumber ∧
      AlmostDisjoint (triangleFamily S) ∧ ¬ FinIntersecting (triangleFamily S) ∧
      #(triangleFamily S) = splittingNumber := by
  obtain ⟨S, hS, hc, hr⟩ := exists_minimal_regular_splitting
  exact ⟨S, hS, hc, triangleFamily_almostDisjoint hS hr, triangleFamily_not_finIntersecting hS,
    (triangleFamily_card hS hr).trans hc⟩

end InfinitaryCombinatorics.Formalizations.R0

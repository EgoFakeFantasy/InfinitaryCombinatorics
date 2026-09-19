import Formalizations.R0.Selectors

namespace InfinitaryCombinatorics.Formalizations.R0
open Set Cardinal
open _root_.R0

noncomputable def blockSize {X : Type} (C : FinSequence X) (n : ℕ) : ℕ :=
  @Fintype.card (C.block n) (C.finite n).fintype

noncomputable def blockEquiv {X : Type} (C : FinSequence X) (n : ℕ) :
    C.block n ≃ Fin (blockSize C n) :=
  @Fintype.equivFin (C.block n) (C.finite n).fintype

lemma blockSize_pos {X : Type} (C : FinSequence X) (n : ℕ) : 0 < blockSize C n := by
  letI := (C.finite n).fintype
  letI : Nonempty (C.block n) := (C.nonempty n).to_subtype
  exact Fintype.card_pos

noncomputable def growingSelector {X : Type} (C : FinSequence X) (s : Set ℕ) (n : ℕ) : X :=
  ((blockEquiv C n).symm ⟨prefixValue s (Nat.log 2 (blockSize C n)),
    (prefixValue_lt _ _).trans_le (Nat.pow_log_le_self 2 (blockSize_pos C n).ne')⟩).val

lemma growingSelector_mem {X : Type} (C : FinSequence X) (s : Set ℕ) (n : ℕ) :
    growingSelector C s n ∈ C.block n := Subtype.property _

lemma growingSelector_eventually_ne {X : Type} (C : FinSequence X)
    (hg : ∀ k, ∃ N, ∀ n, N ≤ n → k ≤ blockSize C n) {s t : Set ℕ} (hst : s ≠ t) :
    ∃ N, ∀ n, N ≤ n → growingSelector C s n ≠ growingSelector C t n := by
  obtain ⟨L, hL⟩ := prefixValue_eventually_ne hst
  obtain ⟨N, hN⟩ := hg (2 ^ L)
  refine ⟨N, fun n hn heq => ?_⟩
  have heq' : (blockEquiv C n).symm ⟨prefixValue s (Nat.log 2 (blockSize C n)),
      (prefixValue_lt _ _).trans_le (Nat.pow_log_le_self 2 (blockSize_pos C n).ne')⟩ =
      (blockEquiv C n).symm ⟨prefixValue t (Nat.log 2 (blockSize C n)),
      (prefixValue_lt _ _).trans_le (Nat.pow_log_le_self 2 (blockSize_pos C n).ne')⟩ :=
    Subtype.ext heq
  have hv := congrArg Fin.val ((blockEquiv C n).symm.injective heq')
  exact hL _ ((Nat.le_log_iff_pow_le (by decide) (blockSize_pos C n).ne').mpr (hN n hn)) hv

/-- Paper Lemma 3.3, including distinctness, exact traces, support and at most
one selected point in each block. No uniform bound on the block sizes is used. -/
theorem exact_trace_realization {X H : Type} (C : FinSequence X)
    (hg : ∀ k, ∃ N, ∀ n, N ≤ n → k ≤ blockSize C n)
    (hH : #H ≤ 2 ^ ℵ₀) (U : H → Set (Set ℕ)) (hU : ∀ h, ADFamily (U h)) :
    ∃ A : ((h : H) × U h) → Set X,
      Function.Injective A ∧ ADFamily (range A) ∧
      ∀ p, trace C (A p) = p.2.val ∧ A p ⊆ ⋃ n, C.block n ∧
        ∀ n, (A p ∩ C.block n).Subsingleton := by
  have hc : #H ≤ #(Set ℕ) := by simpa using hH
  obtain ⟨e⟩ := (Cardinal.le_def H (Set ℕ)).mp hc
  let f : H → ℕ → X := fun h => growingSelector C (e h)
  refine ⟨fun p => f p.1 '' p.2.val, selector_realization C f
    (fun h n => growingSelector_mem C (e h) n) ?_ U hU⟩
  intro h k hhk
  exact growingSelector_eventually_ne C hg (fun he => hhk (e.injective he))

end InfinitaryCombinatorics.Formalizations.R0

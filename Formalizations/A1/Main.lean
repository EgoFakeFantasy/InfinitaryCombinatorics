import Formalizations.A1.LocalNumbering

/-!
# The depth-one reduction and its countercolouring

An empty interval in each thinned ladder yields a single colouring which
excludes both orientations of the fixed types. The club and its local
numbering are shared by all ladders.
-/

namespace InfinitaryCombinatorics.Formalizations.A1
open Set Order
noncomputable section

/-- One of the two internal gaps avoids the initial ladder point's label. -/
theorem exists_avoiding_gap (C : LadderSystem) (D : Set Point) (hD : IsCofinal D)
    (β : LimitBelow omegaOne) (m : ℕ) (hm : 1 ≤ m) (hempty : ¬ Hits (thin C) D β m) :
    ∃ j : ℕ, 1 ≤ j ∧ ∀ x : Point,
      (C β).seq j < x.val → x.val < (C β).seq (j + 1) →
      localNumbering D hD x ≠ localNumbering D hD (ladderPoint C β 0) := by
  have hinj : Set.InjOn (localNumbering D hD)
      (Ico (ladderPoint C β (3 * m)) (ladderPoint C β (3 * m + 3))) := by
    apply localNumbering_injOn_empty D hD
    intro x hx hlow hhigh
    apply hempty
    refine ⟨x, hx, hlow, ?_⟩
    change x.val < (C β).seq (3 * (m + 1))
    simpa only [Nat.mul_add, Nat.mul_one] using hhigh
  have hg := two_gaps (localNumbering D hD)
    (ladderPoint_strictMono C β (show 3 * m < 3 * m + 1 by omega))
    (ladderPoint_strictMono C β (show 3 * m + 1 < 3 * m + 2 by omega))
    (ladderPoint_strictMono C β (show 3 * m + 2 < 3 * m + 3 by omega))
    hinj (localNumbering D hD (ladderPoint C β 0))
  rcases hg with hg | hg
  · exact ⟨3 * m, by omega, hg⟩
  · exact ⟨3 * m + 1, by omega, hg⟩

/-- Only one empty thinned interval at index at least one is needed per ladder. -/
theorem antiColoring_of_empty_intervals (C : LadderSystem) (D : Set Point)
    (hD : IsCofinal D) (hbad : ∀ β, ∃ m ≥ 1, ¬ Hits (thin C) D β m) :
    ∃ f : LimitBelow omegaOne → ℕ, ∀ α β k, f α = k → f β = k →
      ¬ ((typeSeqW k).Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1)) ∨
        (typeSeqW k).swap.Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1))) := by
  classical
  have hg : ∀ β : LimitBelow omegaOne, ∃ j : ℕ, 1 ≤ j ∧ ∀ x : Point,
      (C β).seq j < x.val → x.val < (C β).seq (j + 1) →
      localNumbering D hD x ≠ localNumbering D hD (ladderPoint C β 0) := by
    intro β
    obtain ⟨m, hm, hempty⟩ := hbad β
    exact exists_avoiding_gap C D hD β m hm hempty
  choose j hjpos hjgap using hg
  let q : LimitBelow omegaOne → ℕ := fun β => localNumbering D hD (ladderPoint C β 0)
  let f : LimitBelow omegaOne → ℕ := fun β => cantorPair (j β - 1) (q β)
  have decode (β : LimitBelow omegaOne) (k : ℕ) (hf : f β = k) :
      jk k = j β ∧ cantorSnd k = q β := by
    change cantorPair (j β - 1) (q β) = k at hf
    rw [← hf]
    constructor
    · dsimp only [jk]
      rw [cantorFst_pair]
      have := hjpos β
      omega
    · exact cantorSnd_pair _ _
  have excludes (α β : LimitBelow omegaOne) (k : ℕ) (hα : f α = k) (hβ : f β = k) :
      ¬ (typeSeqW k).Realizes ((C α).initialSegment (widthSeq k + 1))
        ((C β).initialSegment (widthSeq k + 1)) := by
    intro hreal
    have horder := typeSeq_order k hreal
    have ha := (decode α k hα).1
    have hq : q β = q α := (decode β k hβ).2.symm.trans (decode α k hα).2
    apply hjgap α (ladderPoint C β 0)
    · simpa only [Ladder.initialSegment, ha] using horder.1
    · simpa only [Ladder.initialSegment, ha] using horder.2.1
    · exact hq
  refine ⟨f, ?_⟩
  intro α β k hα hβ hreal
  rcases hreal with hreal | hreal
  · exact excludes α β k hα hβ hreal
  · exact excludes β α k hβ hα ((DisjointType.realizes_swap _ _ _).mp hreal)

/-- The proof gives the uniform starting index one for the thinned ladder. -/
theorem typeGuessing_implies_hits_thin (C : LadderSystem)
    (hC : TypeGuessing C widthSeq typeSeqW) (D : Set Point) (hD : IsClub D) :
    ∃ β, ∀ m ≥ 1, Hits (thin C) D β m := by
  classical
  by_contra hbad
  push Not at hbad
  obtain ⟨f, hf⟩ := antiColoring_of_empty_intervals C D hD.isCofinal hbad
  obtain ⟨α, β, k, _, hα, hβ, hreal⟩ := hC f
  exact hf α β k hα hβ hreal

/-- The object-level reduction, with the explicit threefold thinning. -/
theorem typeGuessing_implies_K_thin (C : LadderSystem)
    (hC : TypeGuessing C widthSeq typeSeqW) : K (thin C) := by
  intro D hD
  obtain ⟨β, hβ⟩ := typeGuessing_implies_hits_thin C hC D hD
  exact ⟨β, 1, hβ⟩
/-- Theorem 5.1, closing the existential ladder-system quantifier. -/
theorem G_implies_KA : G → KA := by
  rintro ⟨C, hC⟩
  exact ⟨thin C, typeGuessing_implies_K_thin C hC⟩

theorem BDTG_implies_G : BDTG → G := fun h => h widthSeq typeSeqW typeSeqW_boundedDepth

theorem BDTG_implies_KA : BDTG → KA := fun h => G_implies_KA (BDTG_implies_G h)

theorem not_G_of_not_KA (h : ¬ KA) : ¬ G := fun hG => h (G_implies_KA hG)

theorem not_BDTG_of_not_KA (h : ¬ KA) : ¬ BDTG := fun hB => h (BDTG_implies_KA hB)

/-- Under failure of KA every ladder system has a countercolouring. -/
theorem antiColoring_of_not_KA (h : ¬ KA) (C : LadderSystem) :
    ∃ f : LimitBelow omegaOne → ℕ, ∀ α β k, f α = k → f β = k →
      ¬ ((typeSeqW k).Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1)) ∨
        (typeSeqW k).swap.Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1))) := by
  have hK : ¬ K (thin C) := fun hK => h ⟨thin C, hK⟩
  obtain ⟨D, hD, hbad⟩ := (not_K_iff (thin C)).mp hK
  exact antiColoring_of_empty_intervals C D hD.isCofinal (fun β => hbad β 1)

/-- Corollary 6.2 with a colouring on the full first uncountable ordinal. -/
theorem antiColoring_on_omegaOne (h : ¬ KA) (C : LadderSystem) :
    ∃ f : Point → ℕ, ∀ α β k, f (limitPoint α) = k → f (limitPoint β) = k →
      ¬ ((typeSeqW k).Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1)) ∨
        (typeSeqW k).swap.Realizes ((C α).initialSegment (widthSeq k + 1))
          ((C β).initialSegment (widthSeq k + 1))) := by
  obtain ⟨f, hf⟩ := antiColoring_of_not_KA h C
  refine ⟨extendColoring f, ?_⟩
  intro α β k hα hβ
  exact hf α β k (by simpa using hα) (by simpa using hβ)
end
end InfinitaryCombinatorics.Formalizations.A1

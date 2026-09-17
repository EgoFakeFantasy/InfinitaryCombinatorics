import R0.SplittingNumber
import R0.TreeConstruction
import R0.Transport

namespace R0
open Set Cardinal

lemma aleph0_le_splittingNumber : ℵ₀ ≤ splittingNumber := by
  obtain ⟨S, hS, hcard⟩ := exists_minimal_splitting
  letI : Infinite S := hS.infinite.to_subtype
  rw [← hcard]
  exact Cardinal.aleph0_le_mk S

/-- Removing finite and cofinite members leaves the splitting property unchanged.
In particular the minimum agrees with the standard convention using only
infinite (indeed infinite coinfinite) subsets of the natural numbers. -/
theorem exists_minimal_regular_splitting :
    ∃ S : Set (Set ℕ), Splitting S ∧ #S = splittingNumber ∧
      ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite := by
  obtain ⟨S, hS, hcard⟩ := exists_minimal_splitting
  let T : Set (Set ℕ) := {s | s ∈ S ∧ s.Infinite ∧ sᶜ.Infinite}
  have hT : Splitting T := by
    intro i hi
    obtain ⟨s, hs, hsp⟩ := hS i hi
    refine ⟨s, ⟨hs, hsp.1.mono inter_subset_right, ?_⟩, hsp⟩
    exact hsp.2.mono (fun _ hx => hx.2)
  refine ⟨T, hT, le_antisymm ?_ (splittingNumber_le hT), ?_⟩
  · calc
      #T ≤ #S := Cardinal.mk_le_mk_of_subset (fun _ hs => hs.1)
      _ = splittingNumber := hcard
  · intro s hs
    exact hs.2

lemma treeFamily_card_le {S : Set (Set ℕ)} (hS : Splitting S) : #(treeFamily S) ≤ #S := by
  letI : Infinite S := hS.infinite.to_subtype
  have hω : ℵ₀ ≤ #S := Cardinal.aleph0_le_mk S
  have htwo : (2 : Cardinal) ≤ #S := (Cardinal.natCast_le_aleph0 (n := 2)).trans hω
  calc
    #(treeFamily S) ≤ #(S × Bool) := Cardinal.mk_range_le
    _ = #S * 2 := by simp only [Cardinal.mk_prod, Cardinal.mk_bool, Cardinal.lift_id]
    _ = #S := Cardinal.mul_eq_left hω htwo (by simp)

lemma treeFamily_almostDisjoint {S : Set (Set ℕ)} (hS : Splitting S)
    (hreg : ∀ s ∈ S, s.Infinite ∧ sᶜ.Infinite) : AlmostDisjoint (treeFamily S) := by
  have hnot := treeFamily_not_finIntersecting hS
  have hω : ℵ₀ ≤ #(treeFamily S) :=
    aleph0_le_splittingNumber.trans (splittingNumber_le_of_not_finIntersecting hnot)
  have hinf : (treeFamily S).Infinite :=
    Set.infinite_coe_iff.mp (Cardinal.aleph0_le_mk_iff.mp hω)
  refine ⟨hinf, ?_, ?_⟩
  · rintro a ⟨⟨s, b⟩, rfl⟩
    exact half_infinite (hreg s.val s.property).1 (hreg s.val s.property).2 b
  · rintro a ⟨⟨s, b⟩, rfl⟩ d ⟨⟨t, c⟩, rfl⟩ had
    by_cases hst : s = t
    · subst t
      exact half_inter_same s.val (fun hbc => had (congrArg (half s.val) hbc))
    · exact half_inter_of_ne (fun heq => hst (Subtype.ext heq)) b c

/-- Countability is used only to transfer the constructed family to the natural
numbers. The image lemmas prove that this preserves all relevant properties. -/
noncomputable def nodeEquivNat : Node ≃ ℕ := Classical.choice inferInstance

/-- ZFC upper bound, with no extra relation between cardinal characteristics. -/
theorem exists_non_finIntersecting_ad_of_size_splittingNumber :
    ∃ A : Set (Set ℕ), AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = splittingNumber := by
  obtain ⟨S, hS, hcard, hreg⟩ := exists_minimal_regular_splitting
  let B := treeFamily S
  let e : Node ↪ ℕ := nodeEquivNat.toEmbedding
  let A : Set (Set ℕ) := Set.image e '' B
  have hAD : AlmostDisjoint A := almostDisjoint_map e (treeFamily_almostDisjoint hS hreg)
  have hnot : ¬ FinIntersecting A := not_finIntersecting_map e (treeFamily_not_finIntersecting hS)
  refine ⟨A, hAD, hnot, le_antisymm ?_ (splittingNumber_le_of_not_finIntersecting hnot)⟩
  calc
    #A = #B := Cardinal.mk_image_eq e.injective.image_injective
    _ ≤ #S := treeFamily_card_le hS
    _ = splittingNumber := hcard

def counterexampleCardinals : Set Cardinal :=
  {κ | ∃ A : Set (Set ℕ), AlmostDisjoint A ∧ ¬ FinIntersecting A ∧ #A = κ}

/-- Exact minimum, including attainment, rather than only a conditional bound. -/
theorem splittingNumber_isLeast : IsLeast counterexampleCardinals splittingNumber := by
  refine ⟨exists_non_finIntersecting_ad_of_size_splittingNumber, ?_⟩
  rintro κ ⟨A, _, hnot, hcard⟩
  rw [← hcard]
  exact splittingNumber_le_of_not_finIntersecting hnot

noncomputable def nonFinIntersectingNumber : Cardinal := sInf counterexampleCardinals

/-- The main equality in the R0 manuscript, equation (1.1). -/
theorem nonFinIntersectingNumber_eq_splittingNumber :
    nonFinIntersectingNumber = splittingNumber :=
  splittingNumber_isLeast.csInf_eq

end R0

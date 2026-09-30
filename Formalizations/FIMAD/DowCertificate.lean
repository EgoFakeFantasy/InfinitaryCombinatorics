import Formalizations.FIMAD.DowBoolean
import Formalizations.FIMAD.BooleanEnumeration

/-! The shared graph-name splitting contract is discharged by the proved Dow
Boolean preservation argument, including all countability and infinitude claims. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
open Set PosetRegular

theorem infinite_iff_natUnbounded (X : Set ℕ) : X.Infinite ↔ NatUnbounded X := by
  constructor
  · intro h N
    obtain ⟨k, hk, hN⟩ := infinite_tail_point h N
    exact ⟨k, hN, hk⟩
  · intro h hf
    obtain ⟨m, hm⟩ := hf.bddAbove
    obtain ⟨k, hk, hX⟩ := h (m + 1)
    exact (Nat.not_succ_le_self m) (hk.trans (hm hX))

/-- The precise hypothesis used by the typed graph-name application. -/
theorem splittingCertificate (A : Set (Set ℕ)) : SplittingCertificate (forcingOrder A) := by
  intro v htotal hlower
  obtain ⟨F, hF, hFi, hgood⟩ := boolean_splitting_tests v htotal hlower
  obtain ⟨tests, htests⟩ := (hF.insert univ).exists_eq_range (by simp)
  refine ⟨fun n => tests n, ?_, ?_⟩
  · intro n
    dsimp only
    apply (infinite_iff_natUnbounded _).mp
    have hn : tests n ∈ insert univ F := by rw [htests]; exact mem_range_self n
    rcases mem_insert_iff.mp hn with he | hf
    · rw [he]; exact infinite_univ
    · exact hFi _ hf
  · intro B hB j N
    apply hgood B ?_ j N
    intro X hX
    have hm : X ∈ range tests := htests ▸ mem_insert_of_mem univ hX
    obtain ⟨n, rfl⟩ := hm
    exact ⟨(infinite_iff_natUnbounded _).mpr (hB n).1,
      (infinite_iff_natUnbounded _).mpr (hB n).2⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing

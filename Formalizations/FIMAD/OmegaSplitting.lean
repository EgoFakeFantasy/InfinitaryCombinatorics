import Formalizations.FIMAD.DowCardinal

/-! Simultaneous splitting and the cardinal configuration used by the paper.
The configuration is an explicit hypothesis; no forcing model is postulated. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD
open Set Cardinal
open InfinitaryCombinatorics.Formalizations.R0 (almostDisjointnessNumber)

noncomputable def risingSelector (Y : ℕ → Set ℕ) (hY : ∀ n, (Y n).Infinite) : ℕ → ℕ
  | 0 => (hY 0).nonempty.choose
  | n + 1 => (infinite_exists_gt (hY (n + 1)) (risingSelector Y hY n)).choose

lemma risingSelector_mem (Y : ℕ → Set ℕ) (hY : ∀ n, (Y n).Infinite) (n : ℕ) :
    risingSelector Y hY n ∈ Y n := by
  cases n with
  | zero => exact (hY 0).nonempty.choose_spec
  | succ n => exact (infinite_exists_gt (hY (n + 1)) (risingSelector Y hY n)).choose_spec.1

lemma risingSelector_strictMono (Y : ℕ → Set ℕ) (hY : ∀ n, (Y n).Infinite) :
    StrictMono (risingSelector Y hY) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (infinite_exists_gt (hY (n + 1)) (risingSelector Y hY n)).choose_spec.2

/-- One set splits every member of a countable sequence of infinite sets. -/
theorem exists_simultaneous_splitter (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Infinite) :
    ∃ S : Set ℕ, ∀ n, R0.Splits S (A n) := by
  classical
  let e : (ℕ × ℕ × Bool) ≃ ℕ := Classical.choice inferInstance
  let Y : ℕ → Set ℕ := fun k => A (e.symm k).1
  have hY : ∀ k, (Y k).Infinite := fun k => hA (e.symm k).1
  let f := risingSelector Y hY
  have hf : Function.Injective f := (risingSelector_strictMono Y hY).injective
  let S : Set ℕ := range (fun p : ℕ × ℕ => f (e (p.1, p.2, false)))
  refine ⟨S, fun n => ⟨?_, ?_⟩⟩
  · have hinj : Function.Injective (fun k : ℕ => f (e (n, k, false))) := by
      intro k l h
      exact congrArg (fun p : ℕ × ℕ × Bool => p.2.1) (e.injective (hf h))
    apply (infinite_range_of_injective hinj).mono
    rintro x ⟨k, rfl⟩
    refine ⟨?_, ⟨(n, k), rfl⟩⟩
    simpa only [Y, Equiv.symm_apply_apply] using risingSelector_mem Y hY (e (n, k, false))
  · have hinj : Function.Injective (fun k : ℕ => f (e (n, k, true))) := by
      intro k l h
      exact congrArg (fun p : ℕ × ℕ × Bool => p.2.1) (e.injective (hf h))
    apply (infinite_range_of_injective hinj).mono
    rintro x ⟨k, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [Y, Equiv.symm_apply_apply] using risingSelector_mem Y hY (e (n, k, true))
    · rintro ⟨p, hp⟩
      have hbool := congrArg (fun q : ℕ × ℕ × Bool => q.2.2) (e.injective (hf hp))
      cases hbool

def OmegaSplitting (S : Set (Set ℕ)) : Prop :=
  ∀ A : ℕ → Set ℕ, (∀ n, (A n).Infinite) → ∃ s ∈ S, ∀ n, R0.Splits s (A n)

def omegaSplittingCardinals : Set Cardinal :=
  {κ | ∃ S : Set (Set ℕ), OmegaSplitting S ∧ #S = κ}

noncomputable def omegaSplittingNumber : Cardinal := sInf omegaSplittingCardinals

theorem omegaSplitting_univ : OmegaSplitting (univ : Set (Set ℕ)) := by
  intro A hA
  obtain ⟨s, hs⟩ := exists_simultaneous_splitter A hA
  exact ⟨s, mem_univ _, hs⟩

theorem omegaSplittingCardinals_nonempty : omegaSplittingCardinals.Nonempty :=
  ⟨#(univ : Set (Set ℕ)), univ, omegaSplitting_univ, rfl⟩

theorem exists_minimum_omegaSplitting :
    ∃ S : Set (Set ℕ), OmegaSplitting S ∧ #S = omegaSplittingNumber :=
  csInf_mem omegaSplittingCardinals_nonempty

theorem OmegaSplitting.splitting {S : Set (Set ℕ)} (hS : OmegaSplitting S) : R0.Splitting S := by
  intro A hA
  obtain ⟨s, hs, hsplit⟩ := hS (fun _ => A) (fun _ => hA)
  exact ⟨s, hs, hsplit 0⟩

theorem splittingNumber_le_omegaSplittingNumber :
    R0.splittingNumber ≤ omegaSplittingNumber := by
  obtain ⟨S, hS, hc⟩ := exists_minimum_omegaSplitting
  exact hc ▸ R0.splittingNumber_le hS.splitting

theorem omegaSplittingNumber_le_continuum : omegaSplittingNumber ≤ 2 ^ ℵ₀ := by
  have h : omegaSplittingNumber ≤ #(univ : Set (Set ℕ)) :=
    csInf_le' ⟨univ, omegaSplitting_univ, rfl⟩
  simpa using h

theorem no_fi_mad_of_omegaSplitting_lt_dp (h : omegaSplittingNumber < dowNumber) :
    ¬ ∃ A : Set (Set ℕ), MAD A ∧ R0.FinIntersecting A :=
  no_fi_mad_of_s_lt_dp (splittingNumber_le_omegaSplittingNumber.trans_lt h)

theorem almostDisjointnessNumber_le_continuum :
    almostDisjointnessNumber ≤ 2 ^ ℵ₀ := by
  obtain ⟨A, hA, hc⟩ := InfinitaryCombinatorics.Formalizations.R0.exists_minimum_mad_nat
  have h : #A ≤ #(Set ℕ) := Cardinal.mk_subtype_le _
  simpa only [hc, Cardinal.mk_set, Cardinal.mk_nat] using h

/-- All characteristic values actually used in the paper follow from the
BMZ configuration; the configuration's relative consistency remains upstream. -/
theorem consequences_of_bmz_configuration
    (hs : omegaSplittingNumber = ℵ₁)
    (hd : dowNumber = 2 ^ ℵ₀) (hc : (2 : Cardinal.{0}) ^ ℵ₀ = Cardinal.aleph 2) :
    R0.splittingNumber = ℵ₁ ∧
    almostDisjointSeparationNumber = 2 ^ ℵ₀ ∧
    boundingNumber = 2 ^ ℵ₀ ∧ almostDisjointnessNumber = 2 ^ ℵ₀ ∧
    ¬ ∃ A : Set (Set ℕ), MAD A ∧ R0.FinIntersecting A := by
  have hs' : R0.splittingNumber = ℵ₁ := le_antisymm
    (hs ▸ splittingNumber_le_omegaSplittingNumber) aleph_one_le_splittingNumber
  have hca : 2 ^ ℵ₀ ≤ almostDisjointSeparationNumber :=
    hd ▸ dowNumber_le_almostDisjointSeparationNumber
  have hab := almostDisjointSeparationNumber_le_boundingNumber
  have hba := boundingNumber_le_almostDisjointnessNumber
  have hac := almostDisjointnessNumber_le_continuum
  refine ⟨hs', le_antisymm (hab.trans (hba.trans hac)) hca,
    le_antisymm (hba.trans hac) (hca.trans hab),
    le_antisymm hac (hca.trans (hab.trans hba)), ?_⟩
  apply no_fi_mad_of_omegaSplitting_lt_dp
  rw [hs, hd, hc]
  exact Cardinal.aleph_lt_aleph.mpr one_lt_two

end InfinitaryCombinatorics.Formalizations.FIMAD

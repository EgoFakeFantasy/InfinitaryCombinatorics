import Formalizations.FIMAD.StandardCoding

/-! Both directions of the correspondence between internal finite-block
sequences and host sequences, including all their retained traces. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Standard
universe u
open Set

noncomputable def sequence (D : R0.FinSequence ℕ) : ZFSet.{u} :=
  ZFSet.range (fun n => ZFSet.pair (nat n) (real (D.block n)))

theorem value_sequence (D : R0.FinSequence ℕ) (x b : ZFSet.{u}) :
    Internal.Value mem (sequence D) x b ↔ ∃ n, x = nat n ∧ b = real (D.block n) := by
  simp [value_iff, sequence, ZFSet.mem_range, ZFSet.pair_inj, eq_comm]

theorem value_sequence_nat (D : R0.FinSequence ℕ) (n : ℕ) (b : ZFSet.{u}) :
    Internal.Value mem (sequence D) (nat n) b ↔ b = real (D.block n) := by
  simp [value_sequence, nat_injective.eq_iff]

theorem finSequence_sequence (D : R0.FinSequence ℕ) :
    Internal.FinSequence mem ZFSet.omega (sequence.{u} D) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨n, rfl⟩ := ZFSet.mem_range.mp hp
    exact ⟨nat n, real (D.block n), nat_mem_omega n, (pair_iff _ _ _).mpr rfl⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := mem_omega.mp hx
    exact ⟨real (D.block n), (value_sequence_nat _ _ _).mpr rfl,
      fun b hb => (value_sequence_nat _ _ _).mp hb⟩
  · intro x b _ hb
    obtain ⟨n, rfl, rfl⟩ := (value_sequence _ _ _).mp hb
    exact ⟨real_subset_omega _, (finite_real _).mpr (D.finite n),
      (nonempty_real _).mpr (D.nonempty n)⟩
  · intro x y b d _ _ hne hb hd
    obtain ⟨n, rfl, rfl⟩ := (value_sequence _ _ _).mp hb
    obtain ⟨m, rfl, rfl⟩ := (value_sequence _ _ _).mp hd
    rintro ⟨z, hz, hz'⟩
    obtain ⟨k, hk, rfl⟩ := mem_real.mp hz
    exact Set.disjoint_left.mp (D.disjoint n m (fun h => hne (congrArg nat h))) hk
      ((nat_mem_real _ _).mp hz')

/-- Every internal finite-block sequence in the standard universe is decoded;
there is no bound on block sizes and no restriction on the sequence graph. -/
theorem decode_sequence {C : ZFSet.{u}}
    (hC : Internal.FinSequence mem ZFSet.omega C) :
    ∃ D : R0.FinSequence ℕ, ∀ n b,
      Internal.Value mem C (nat n) b ↔ b = real (D.block n) := by
  classical
  let b : ℕ → ZFSet := fun n => (hC.1.2 (nat n) (nat_mem_omega n)).choose
  have hb (n) : Internal.Value mem C (nat n) (b n) :=
    (hC.1.2 (nat n) (nat_mem_omega n)).choose_spec.1
  have hu (n) (z) (hz : Internal.Value mem C (nat n) z) : z = b n :=
    (hC.1.2 (nat n) (nat_mem_omega n)).choose_spec.2 z hz
  have hp (n) := hC.2.1 (nat n) (b n) (nat_mem_omega n) (hb n)
  have heq (n) : real (decode (b n)) = b n := real_decode (hp n).1
  let D : R0.FinSequence ℕ := {
    block := fun n => decode (b n)
    finite := fun n => (finite_real _).mp ((heq n).symm ▸ (hp n).2.1)
    nonempty := fun n => (nonempty_real _).mp ((heq n).symm ▸ (hp n).2.2)
    disjoint := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      intro k hkn hkm
      exact hC.2.2 (nat n) (nat m) (b n) (b m) (nat_mem_omega n) (nat_mem_omega m)
        (fun h => hnm (nat_injective h)) (hb n) (hb m) ⟨nat k, hkn, hkm⟩ }
  refine ⟨D, fun n z => ?_⟩
  change Internal.Value mem C (nat n) z ↔ z = real (decode (b n))
  rw [heq]
  exact ⟨hu n z, fun h => h ▸ hb n⟩

theorem traceAt_nat {C : ZFSet.{u}} {D : R0.FinSequence ℕ}
    (hval : ∀ n b, Internal.Value mem C (nat n) b ↔ b = real (D.block n))
    (s : Set ℕ) (n : ℕ) : Internal.TraceAt mem C (real s) (nat n) ↔ n ∈ R0.trace D s := by
  simp only [Internal.TraceAt, hval, exists_eq_left]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨k, hk, rfl⟩ := mem_real.mp hx
    exact ⟨k, hk, (nat_mem_real _ _).mp hy⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨nat k, (nat_mem_real _ _).mpr hk, (nat_mem_real _ _).mpr hk'⟩

theorem restrictedTrace_iff {C : ZFSet.{u}} {D : R0.FinSequence ℕ}
    (hval : ∀ n b, Internal.Value mem C (nat n) b ↔ b = real (D.block n))
    (t : ZFSet.{u}) (I s : Set ℕ) :
    Internal.RestrictedTrace mem t C (real I) (real s) ↔ t = real (I ∩ R0.trace D s) := by
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨hi, ht⟩ := (h x).mp hx
      obtain ⟨n, hn, rfl⟩ := mem_real.mp hi
      exact (nat_mem_real _ _).mpr ⟨hn, (traceAt_nat hval s n).mp ht⟩
    · intro hx
      obtain ⟨n, hn, rfl⟩ := mem_real.mp hx
      exact (h _).mpr ⟨(nat_mem_real _ _).mpr hn.1, (traceAt_nat hval s n).mpr hn.2⟩
  · rintro rfl x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := mem_real.mp hx
      exact ⟨(nat_mem_real _ _).mpr hn.1, (traceAt_nat hval s n).mpr hn.2⟩
    · rintro ⟨hi, ht⟩
      obtain ⟨n, hn, rfl⟩ := mem_real.mp hi
      exact (nat_mem_real _ _).mpr ⟨hn, (traceAt_nat hval s n).mp ht⟩

theorem retained_iff {C : ZFSet.{u}} {D : R0.FinSequence ℕ}
    (hval : ∀ n b, Internal.Value mem C (nat n) b ↔ b = real (D.block n))
    (I s : Set ℕ) : Internal.Retained mem ZFSet.omega C (real I) (real s) ↔
      (I ∩ R0.trace D s).Infinite := by
  simp only [Internal.Retained, restrictedTrace_iff hval, exists_eq_left, infinite_real]

theorem commonTrace_iff {C : ZFSet.{u}} {D : R0.FinSequence ℕ}
    (hval : ∀ n b, Internal.Value mem C (nat n) b ↔ b = real (D.block n))
    (t : ZFSet.{u}) (I : Set ℕ) (F : Set (Set ℕ)) :
    Internal.CommonTrace mem t C (real I) (family F) ↔
      t = real (I ∩ ⋂ s ∈ F, R0.trace D s) := by
  have hn (n : ℕ) :
      (∀ a, mem a (family.{u} F) → Internal.TraceAt mem C a (nat n)) ↔
        n ∈ ⋂ s ∈ F, R0.trace D s := by
    constructor
    · intro h
      exact mem_iInter₂.mpr fun s hs => (traceAt_nat hval s n).mp
        (h (real s) ((real_mem_family _ _).mpr hs))
    · intro h a ha
      obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
      exact (traceAt_nat hval s n).mpr (mem_iInter₂.mp h s hs)
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨hi, ht⟩ := (h x).mp hx
      obtain ⟨n, hni, rfl⟩ := mem_real.mp hi
      exact (nat_mem_real _ _).mpr ⟨hni, (hn n).mp ht⟩
    · intro hx
      obtain ⟨n, hni, rfl⟩ := mem_real.mp hx
      exact (h _).mpr ⟨(nat_mem_real _ _).mpr hni.1, (hn n).mpr hni.2⟩
  · rintro rfl x
    constructor
    · intro hx
      obtain ⟨n, hni, rfl⟩ := mem_real.mp hx
      exact ⟨(nat_mem_real _ _).mpr hni.1, (hn n).mpr hni.2⟩
    · rintro ⟨hi, ht⟩
      obtain ⟨n, hni, rfl⟩ := mem_real.mp hi
      exact (nat_mem_real _ _).mpr ⟨hni, (hn n).mp ht⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.Standard

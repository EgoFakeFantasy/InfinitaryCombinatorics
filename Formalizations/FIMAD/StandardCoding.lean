import Formalizations.FIMAD.StandardSemantics
import Formalizations.FIMAD.MemberwiseSemantics
import Formalizations.FIMAD.Nonexistence

/-! Coding all subsets of the standard natural numbers and all families of
such subsets as actual sets. No restriction to countable families is imposed. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Standard
universe u
open Set

noncomputable def real (s : Set ℕ) : ZFSet.{u} := ZFSet.range (fun n : s => nat n.val)

theorem mem_real {s : Set ℕ} {x : ZFSet.{u}} :
    x ∈ real s ↔ ∃ n ∈ s, x = nat n := by
  simp [real, ZFSet.mem_range, eq_comm]

@[simp] theorem nat_mem_real (s : Set ℕ) (n : ℕ) : nat.{u} n ∈ real s ↔ n ∈ s := by
  simp [mem_real, nat_injective.eq_iff]

theorem coe_real (s : Set ℕ) : (real.{u} s : Set ZFSet) = nat '' s := by
  ext x
  simp [mem_real, eq_comm]

theorem real_injective : Function.Injective real.{u} := by
  intro s t h
  ext n
  exact (nat_mem_real s n).symm.trans ((congrArg (fun a => nat n ∈ a) h).to_iff.trans
    (nat_mem_real t n))

def decode (a : ZFSet.{u}) : Set ℕ := {n | nat n ∈ a}

@[simp] theorem decode_real (s : Set ℕ) : decode (real.{u} s) = s := by
  ext n
  exact nat_mem_real s n

theorem real_decode {a : ZFSet.{u}} (ha : Internal.Subset mem a ZFSet.omega) :
    real (decode a) = a := by
  apply ZFSet.ext
  intro x
  constructor
  · rintro hx
    obtain ⟨n, hn, rfl⟩ := mem_real.mp hx
    exact hn
  · intro hx
    obtain ⟨n, rfl⟩ := mem_omega.mp (ha x hx)
    exact (nat_mem_real _ _).mpr hx

theorem real_subset_omega (s : Set ℕ) : Internal.Subset mem (real.{u} s) ZFSet.omega := by
  intro x hx
  obtain ⟨n, _, rfl⟩ := mem_real.mp hx
  exact nat_mem_omega n

theorem real_subset_iff (s t : Set ℕ) : Internal.Subset mem (real.{u} s) (real t) ↔ s ⊆ t := by
  constructor
  · intro h n hn
    exact (nat_mem_real _ _).mp (h _ ((nat_mem_real _ _).mpr hn))
  · intro h x hx
    obtain ⟨n, hn, rfl⟩ := mem_real.mp hx
    exact (nat_mem_real _ _).mpr (h hn)

theorem finite_real (s : Set ℕ) : Internal.Finite mem ZFSet.omega (real.{u} s) ↔ s.Finite := by
  rw [finite_iff, coe_real, finite_image_iff nat_injective.injOn]

theorem infinite_real (s : Set ℕ) : Internal.Infinite mem ZFSet.omega (real.{u} s) ↔ s.Infinite :=
  not_congr (finite_real s)

theorem nonempty_real (s : Set ℕ) : Internal.Nonempty mem (real.{u} s) ↔ s.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn, _⟩ := mem_real.mp hx
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨nat n, (nat_mem_real _ _).mpr hn⟩

theorem real_inter (s t : Set ℕ) : real.{u} (s ∩ t) = real s ∩ real t := by
  apply ZFSet.ext
  intro x
  simp only [mem_real, ZFSet.mem_inter, mem_inter_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn.1, rfl⟩, ⟨n, hn.2, rfl⟩⟩
  · rintro ⟨⟨n, hn, rfl⟩, ⟨m, hm, heq⟩⟩
    exact ⟨n, ⟨hn, nat_injective heq ▸ hm⟩, rfl⟩

theorem inter_iff (d a b : ZFSet.{u}) : Internal.Inter mem d a b ↔ d = a ∩ b := by
  simp only [Internal.Inter, mem, ZFSet.ext_iff, ZFSet.mem_inter]

theorem finite_inter_real (s t : Set ℕ) :
    (∃ d, Internal.Inter mem d (real.{u} s) (real t) ∧
      Internal.Finite mem ZFSet.omega d) ↔ (s ∩ t).Finite := by
  simp only [inter_iff, exists_eq_left, ← real_inter, finite_real]

theorem infinite_inter_real (s t : Set ℕ) :
    Internal.InfiniteInter mem ZFSet.omega (real.{u} s) (real t) ↔ (s ∩ t).Infinite := by
  simp only [Internal.InfiniteInter, inter_iff, exists_eq_left, ← real_inter, infinite_real]

noncomputable def family (A : Set (Set ℕ)) : ZFSet.{u} :=
  ZFSet.range (fun a : A => real a.val)

theorem mem_family {A : Set (Set ℕ)} {a : ZFSet.{u}} :
    a ∈ family A ↔ ∃ s ∈ A, a = real s := by
  simp [family, ZFSet.mem_range, eq_comm]

@[simp] theorem real_mem_family (A : Set (Set ℕ)) (s : Set ℕ) :
    real.{u} s ∈ family A ↔ s ∈ A := by
  simp [mem_family, real_injective.eq_iff]

theorem coe_family (A : Set (Set ℕ)) : (family.{u} A : Set ZFSet) = real '' A := by
  ext x
  simp [mem_family, eq_comm]

theorem finite_family (A : Set (Set ℕ)) :
    Internal.Finite mem ZFSet.omega (family.{u} A) ↔ A.Finite := by
  rw [finite_iff, coe_family, finite_image_iff real_injective.injOn]

theorem infinite_family (A : Set (Set ℕ)) :
    Internal.Infinite mem ZFSet.omega (family.{u} A) ↔ A.Infinite :=
  not_congr (finite_family A)

theorem ad_family (A : Set (Set ℕ)) :
    Internal.AD mem ZFSet.omega (family.{u} A) ↔ R0.AlmostDisjoint A := by
  constructor
  · rintro ⟨hi, hm, hp⟩
    refine ⟨(infinite_family A).mp hi, fun a ha => ?_, fun a ha b hb hne => ?_⟩
    · exact (infinite_real a).mp (hm _ ((real_mem_family _ _).mpr ha)).2
    · exact (finite_inter_real a b).mp (hp _ _ ((real_mem_family _ _).mpr ha)
        ((real_mem_family _ _).mpr hb) (fun h => hne (real_injective h)))
  · rintro ⟨hi, hm, hp⟩
    refine ⟨(infinite_family A).mpr hi, ?_, ?_⟩
    · intro a ha
      obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
      exact ⟨real_subset_omega s, (infinite_real s).mpr (hm s hs)⟩
    · intro a b ha hb hne
      obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
      obtain ⟨t, ht, rfl⟩ := mem_family.mp hb
      exact (finite_inter_real s t).mpr (hp s hs t ht (fun h => hne (congrArg real h)))

/-- Maximality ranges over every internal infinite subset of omega, not merely
over a preselected collection of coded test sets. -/
theorem mad_family (A : Set (Set ℕ)) :
    Internal.MAD mem ZFSet.omega (family.{u} A) ↔ MAD A := by
  constructor
  · rintro ⟨had, hmax⟩
    refine ⟨(ad_family A).mp had, fun x hx => ?_⟩
    obtain ⟨a, ha, hi⟩ := hmax (real x) (real_subset_omega x) ((infinite_real x).mpr hx)
    obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
    exact ⟨s, hs, (infinite_inter_real x s).mp hi⟩
  · rintro ⟨had, hmax⟩
    refine ⟨(ad_family A).mpr had, fun x hx hi => ?_⟩
    have heq := real_decode hx
    obtain ⟨s, hs, hsi⟩ := hmax (decode x) ((infinite_real _).mp (heq.symm ▸ hi))
    exact ⟨real s, (real_mem_family _ _).mpr hs,
      heq ▸ (infinite_inter_real _ s).mpr hsi⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.Standard

import Formalizations.FIMAD.StandardSequences
import Formalizations.FIMAD.CHConstruction
import Formalizations.FIMAD.GeneralConstruction

/-! Exact FI MAD semantics in mathlib's standard set universe. The cardinal
hypotheses in the applications below are host hypotheses. These theorems do
not construct forcing extensions or establish relative consistency over ZFC. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.Standard
universe u
open Set

theorem family_subset_iff (F A : Set (Set ℕ)) :
    Internal.Subset mem (family.{u} F) (family A) ↔ F ⊆ A := by
  constructor
  · intro h s hs
    exact (real_mem_family _ _).mp (h _ ((real_mem_family _ _).mpr hs))
  · intro h a ha
    obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
    exact (real_mem_family _ _).mpr (h hs)

theorem nonempty_family (F : Set (Set ℕ)) :
    Internal.Nonempty mem (family.{u} F) ↔ F.Nonempty := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs, _⟩ := mem_family.mp ha
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨real s, (real_mem_family _ _).mpr hs⟩

def decodeFamily (A : ZFSet.{u}) : Set (Set ℕ) := {s | real s ∈ A}

theorem family_decode {A : ZFSet.{u}}
    (hA : ∀ a, mem a A → Internal.Subset mem a ZFSet.omega) :
    family (decodeFamily A) = A := by
  apply ZFSet.ext
  intro a
  constructor
  · intro ha
    obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
    exact hs
  · intro ha
    have heq := real_decode (hA a ha)
    exact mem_family.mpr ⟨decode a, show real (decode a) ∈ A by rw [heq]; exact ha, heq.symm⟩

theorem decode_subfamily {F : ZFSet.{u}} {A : Set (Set ℕ)}
    (hF : Internal.Subset mem F (family A)) :
    ∃ G : Set (Set ℕ), G ⊆ A ∧ F = family G := by
  have heq : family (decodeFamily F) = F := family_decode (by
    intro a ha
    obtain ⟨s, _, rfl⟩ := mem_family.mp (hF a ha)
    exact real_subset_omega s)
  refine ⟨decodeFamily F, ?_, heq.symm⟩
  intro s hs
  exact (real_mem_family _ _).mp (hF _ hs)

/-- The two full FI predicates agree, including repeated traces and the
discarding of finite traces before testing centeredness. -/
theorem fi_family (A : Set (Set ℕ)) :
    Internal.FI mem ZFSet.omega (family.{u} A) ↔ R0.FinIntersecting A := by
  rw [finIntersecting_iff_memberwise]
  constructor
  · intro h D
    obtain ⟨I, hI, hi, hF⟩ := h (sequence D) (finSequence_sequence D)
    have heq := real_decode hI
    refine ⟨decode I, (infinite_real _).mp (heq.symm ▸ hi), ?_⟩
    intro F hFA hf hne hr
    have hret : ∀ a, mem a (family.{u} F) → Internal.Retained mem ZFSet.omega
        (sequence D) I a := by
      intro a ha
      obtain ⟨s, hs, rfl⟩ := mem_family.mp ha
      rw [← heq]
      exact (retained_iff (value_sequence_nat D) _ _).mpr (hr s hs)
    obtain ⟨t, ht, hti⟩ := hF (family F) ((family_subset_iff F A).mpr hFA)
      ((finite_family F).mpr hf) ((nonempty_family F).mpr hne) hret
    rw [← heq] at ht
    have hteq := (commonTrace_iff (value_sequence_nat D) t (decode I) F).mp ht
    exact (infinite_real _).mp (hteq ▸ hti)
  · intro h C hC
    obtain ⟨D, hval⟩ := decode_sequence hC
    obtain ⟨I, hi, hF⟩ := h D
    refine ⟨real I, real_subset_omega I, (infinite_real I).mpr hi, ?_⟩
    intro F hFA hf hne hr
    obtain ⟨G, hGA, rfl⟩ := decode_subfamily hFA
    have hret : ∀ s ∈ G, (I ∩ R0.trace D s).Infinite := by
      intro s hs
      exact (retained_iff hval I s).mp (hr _ ((real_mem_family G s).mpr hs))
    have hcommon := hF G hGA ((finite_family G).mp hf) ((nonempty_family G).mp hne) hret
    exact ⟨real (I ∩ ⋂ s ∈ G, R0.trace D s), (commonTrace_iff hval _ _ _).mpr rfl,
      (infinite_real _).mpr hcommon⟩

theorem omega_unique {w : ZFSet.{u}} (hw : Internal.Omega mem w) : w = ZFSet.omega := by
  apply ZFSet.ext
  intro x
  exact ⟨hw.2 _ omega.1 x, omega.2 _ hw.1 x⟩

/-- All quantifiers in the internal existence sentence agree with their host
counterparts in the standard well-founded set universe, at every universe level. -/
theorem existsFIMAD_iff : Internal.ExistsFIMAD mem.{u} ↔ ExistsFIMAD := by
  constructor
  · rintro ⟨w, A, hw, hm, hf⟩
    have hw' := omega_unique hw
    subst w
    have heq := family_decode (fun a ha => (hm.1.2.1 a ha).1)
    rw [← heq] at hm hf
    exact ⟨decodeFamily A, (mad_family _).mp hm, (fi_family _).mp hf⟩
  · rintro ⟨A, hm, hf⟩
    exact ⟨ZFSet.omega, family A, omega, (mad_family A).mpr hm, (fi_family A).mpr hf⟩

theorem existsFIMAD_of_CH
    (hCH : (2 : Cardinal.{0}) ^ Cardinal.aleph0 = Cardinal.aleph 1) :
    Internal.ExistsFIMAD mem.{u} :=
  existsFIMAD_iff.mpr (exists_fi_mad_of_CH hCH)

theorem not_existsFIMAD_of_s_lt_ap
    (h : R0.splittingNumber < almostDisjointSeparationNumber) :
    ¬ Internal.ExistsFIMAD mem.{u} :=
  fun he => no_fi_mad_of_s_lt_ap h (existsFIMAD_iff.mp he)

theorem existsFIMAD_of_ap_eq_s_eq_continuum
    (hap : almostDisjointSeparationNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0)
    (hs : R0.splittingNumber = (2 : Cardinal.{0}) ^ Cardinal.aleph0) :
    Internal.ExistsFIMAD mem.{u} :=
  existsFIMAD_iff.mpr (exists_fi_mad_of_ap_eq_s_eq_continuum hap hs)

end InfinitaryCombinatorics.Formalizations.FIMAD.Standard

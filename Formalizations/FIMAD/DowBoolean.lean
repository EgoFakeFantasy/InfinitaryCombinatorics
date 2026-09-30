import Formalizations.FIMAD.DowTallness
import Formalizations.FIMAD.PosetRegular

/-! Dow preservation with truth values in the actual regular-open completion.
Total Boolean-valued natural numbers yield dense decisions by a proved theorem.
The conclusion is top-valued unbounded hitting on both sides of a splitter.
Iteration and the cardinal bookkeeping are separate from this single step. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing
open Set PosetRegular
variable {A : Set (Set ℕ)}

def forcingOrder (A : Set (Set ℕ)) : PosetRegular.Order (Condition A) where
  le := (· ≤ ·)
  refl := le_refl
  trans := le_trans

abbrev Truth (A : Set (Set ℕ)) := PosetRegular.Regular (forcingOrder A)

/-- Membership coefficients of the canonical union-of-stems real. -/
def genericValue (A : Set (Set ℕ)) (k : ℕ) : Truth A :=
  Regular.closure (fun p => k ∈ p.stem)

theorem genericValue_of_mem {p : Condition A} {k : ℕ} (h : k ∈ p.stem) :
    (genericValue A k).mem p :=
  fun q hq => ⟨q, le_refl q, hq.1 h⟩

/-- The Boolean assertion that the generic real meets a arbitrarily high. -/
theorem generic_hits_top {a : Set ℕ} (ha : a ∈ A) (hi : a.Infinite) (N : ℕ) :
    Regular.iSup (fun k : {k : ℕ // k ∈ a ∧ N ≤ k} => genericValue A k.1) =
      Regular.top := by
  apply (Regular.iSup_eq_top_iff _).mpr
  intro p
  obtain ⟨q, ⟨k, hkq, hka, hkN⟩, hq⟩ := hit_dense ha hi N p
  exact ⟨q, hq, ⟨k, hka, hkN⟩, genericValue_of_mem hkq⟩

/-- Truth value of having no B-points outside a specified finite ground set. -/
def avoidsOutside (B : Set ℕ) (s : Finset ℕ) : Truth A :=
  Regular.imp (Regular.iSup
    (fun k : {k : ℕ // k ∈ B ∧ k ∉ s} => genericValue A k.1)) Regular.bot

theorem avoidsOutside_mem {B : Set ℕ} {p : Condition A} (hp : p ∈ avoid B) :
    (avoidsOutside B p.stem).mem p := by
  intro q hq hv
  obtain ⟨r, hr, k, hk⟩ := hv q (le_refl q)
  obtain ⟨t, ht, hkt⟩ := hk r (le_refl r)
  have htp : t ≤ p := ht.trans (hr.trans hq)
  exact htp.2.2 (hp ⟨k.1, hkt, k.2.1, k.2.2⟩)

/-- Finite intersection is forced, without postulating a generic filter. -/
theorem generic_avoids_top (B : Set ℕ) (hB : ∀ a ∈ A, (a ∩ B).Finite) :
    Regular.iSup (avoidsOutside (A := A) B) = Regular.top := by
  apply (Regular.iSup_eq_top_iff _).mpr
  intro p
  obtain ⟨q, hqB, hq⟩ := avoid_dense B hB p
  exact ⟨q, hq, q.stem, avoidsOutside_mem hqB⟩

/-- The regular-open completion inherits the countable chain condition from
the actual Dow poset. Antichains contain only nonzero truth values. -/
theorem boolean_antichain_countable (S : Set (Truth A))
    (hne : ∀ U ∈ S, U ≠ Regular.bot)
    (hdis : ∀ U ∈ S, ∀ V ∈ S, U ≠ V → Regular.meet U V = Regular.bot) :
    S.Countable := by
  classical
  choose p hp using fun U : S => (Regular.nonzero_iff U.1).mp (hne U.1 U.2)
  have inj : Function.Injective p := by
    intro U V he
    by_contra hn
    have hUV : U.1 ≠ V.1 := fun h => hn (Subtype.ext h)
    have hm : (Regular.meet U.1 V.1).mem (p U) := ⟨hp U, he ▸ hp V⟩
    rw [hdis U.1 U.2 V.1 V.2 hUV] at hm
    exact hm
  have hc : (range p).Countable := antichain_countable _ (by
    rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩ hnep ⟨r, hrU, hrV⟩
    have hUV : U.1 ≠ V.1 := fun h => hnep (congrArg p (Subtype.ext h))
    have hm : (Regular.meet U.1 V.1).mem r :=
      ⟨U.1.lower hrU (hp U), V.1.lower hrV (hp V)⟩
    rw [hdis U.1 U.2 V.1 V.2 hUV] at hm
    exact hm)
  haveI : Countable (range p) := hc
  exact Set.countable_coe_iff.mp (Function.Injective.countable
    (f := fun U : S => (⟨p U, mem_range_self U⟩ : range p))
    (fun _ _ h => inj (congrArg Subtype.val h)))

/-- Boolean value of finding a value in B beyond the index N. -/
def hitValue (v : ℕ → ℕ → Truth A) (B : Set ℕ) (N : ℕ) : Truth A :=
  Regular.iSup (fun x : {x : ℕ × ℕ // N ≤ x.1 ∧ x.2 ∈ B} => v x.1.1 x.1.2)

theorem boolean_decisions_dense (v : ℕ → Truth A)
    (htotal : Regular.iSup v = Regular.top) : Dense {p | ∃ k, (v k).mem p} := by
  intro p
  obtain ⟨q, hq, k, hk⟩ := (Regular.iSup_eq_top_iff v).mp htotal p
  exact ⟨q, ⟨k, hk⟩, hq⟩

/-- A countable family of total Boolean enumerations has countable ground
splitting tests. The lower bound is a Boolean assertion: values below the index
have truth value bottom. No decision-density premise is needed. -/
theorem boolean_splitting_tests (v : ℕ → ℕ → ℕ → Truth A)
    (htotal : ∀ j i, Regular.iSup (v j i) = Regular.top)
    (hlower : ∀ j i k, k < i → v j i k = Regular.bot) :
    ∃ F : Set (Set ℕ), F.Countable ∧ (∀ X ∈ F, X.Infinite) ∧
      ∀ B, (∀ X ∈ F, R0.Splits B X) → ∀ j N,
        hitValue (v j) B N = Regular.top ∧
        hitValue (v j) Bᶜ N = Regular.top := by
  have hm : ∀ j i p q, q ≤ p → ∀ k, (v j i k).mem p → (v j i k).mem q :=
    fun j i _ _ h k hk => (v j i k).lower h hk
  have hl : ∀ j i p k, (v j i k).mem p → i ≤ k := by
    intro j i p k hk
    by_contra h
    rw [hlower j i k (Nat.lt_of_not_ge h)] at hk
    exact hk
  obtain ⟨F, hF, hFi, hgood⟩ := simultaneous_splitting_tests
    (fun j i p k => (v j i k).mem p) hm
    (fun j i => boolean_decisions_dense (v j i) (htotal j i)) hl
  refine ⟨F, hF, hFi, fun B hB j N => ⟨?_, ?_⟩⟩
  · apply (Regular.iSup_eq_top_iff _).mpr
    intro p
    obtain ⟨q, ⟨i, hi, k, hk, hv⟩, hq⟩ := (hgood B hB j N).1 p
    exact ⟨q, hq, ⟨(i, k), hi, hk⟩, hv⟩
  · apply (Regular.iSup_eq_top_iff _).mpr
    intro p
    obtain ⟨q, ⟨i, hi, k, hk, hv⟩, hq⟩ := (hgood B hB j N).2 p
    exact ⟨q, hq, ⟨(i, k), hi, hk⟩, hv⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.DowForcing

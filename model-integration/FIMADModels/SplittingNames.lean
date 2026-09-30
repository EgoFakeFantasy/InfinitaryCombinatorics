import FIMADModels.UnboundedNames
import Formalizations.FIMAD.BooleanEnumeration

/-! Applying the shared Boolean splitting contract to actual set names.
The contract is a visible premise here and is proved for the exact Dow order
in the main package. This adapter constructs witnesses and restrictions. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC.Model.Boolean BV_graph
universe u
variable {P : Type u} (R : Order P)

noncomputable def groundReal (B : Nat → Prop) : BV_name (Regular R) := by
  classical
  exact real R (fun k => if B k then (algebra R).top else (algebra R).bot)

noncomputable def restriction (G : BV_name (Regular R)) (B : Nat → Prop) :
    BV_name (Regular R) :=
  sep (algebra R) G (fun Y => bv_mem (algebra R) Y (groundReal R B))

open Classical in
theorem restriction_mem (G : BV_name (Regular R)) (B : Nat → Prop) (k : Nat) :
    bv_mem (algebra R) (natural R k) (restriction R G B) =
      if B k then bv_mem (algebra R) (natural R k) G else (algebra R).bot := by
  classical
  rw [restriction, sep_mem (algebra R) _ _ (stable_elem (algebra R) _)]
  unfold groundReal
  rw [real_mem]
  split <;> simp only [BA_alg.meet_top, BA_alg.meet_bot]

/-- Dense hits of the extracted witnesses imply actual unboundedness of the
restricted set name, with full bounded quantification over graph names. -/
theorem hits_force_unbounded (G : BV_name (Regular R)) (f : Nat → BV_name (Regular R))
    (hlower : ∀ i, atLeast R i (f i) = (algebra R).top)
    (hmem : ∀ i, bv_mem (algebra R) (f i) G = (algebra R).top)
    (B : Nat → Prop)
    (hhit : ∀ N, enumerationHit R
      (fun i k => bv_eq (algebra R) (f i) (natural R k)) B N = Regular.top) :
    unboundedValue R (restriction R G B) = (algebra R).top := by
  rw [unbounded_eq_tails]
  apply ((algebra R).top_le_iff _).mp
  apply ((algebra R).le_iInf_iff _ _).mpr
  intro N
  have he : (algebra R).iSup (fun x : {x : Nat × Nat // N ≤ x.1 ∧ B x.2} =>
      bv_eq (algebra R) (f x.1.1) (natural R x.1.2)) = (algebra R).top := by
    rw [algebra_iSup, algebra_top]
    exact hhit N
  rw [← he]
  apply ((algebra R).iSup_le_iff _ _).mpr
  rintro ⟨⟨i, k⟩, hi, hk⟩
  by_cases hki : i ≤ k
  · have hm := mem_left (algebra R) (f i) (natural R k) G
    rw [hmem i, (algebra R).meet_top] at hm
    apply (algebra R).le_trans hm
    have h := (algebra R).le_iSup
      (fun n : {n : Nat // N ≤ n} => bv_mem (algebra R) (natural R n.1) (restriction R G B))
      ⟨k, Nat.le_trans hi hki⟩
    rwa [restriction_mem, if_pos hk] at h
  · rw [small_value_eq_bot R (f i) i (hlower i) (Nat.lt_of_not_ge hki)]
    exact (algebra R).bot_le _

/-- Every countable collection of unbounded set names has countable ground
splitting tests, provided the proved Boolean splitting contract for its order.
No enumerations, generic filters, or preservation of names are assumed. -/
theorem split_unbounded_names (hSplit : SplittingCertificate R)
    (G : Nat → BV_name (Regular R))
    (hG : ∀ j, unboundedValue R (G j) = (algebra R).top) :
    ∃ tests : Nat → Nat → Prop, (∀ n, NatUnbounded (tests n)) ∧
      ∀ B, (∀ n, NatSplits B (tests n)) → ∀ j,
        unboundedValue R (restriction R (G j) B) = (algebra R).top ∧
        unboundedValue R (restriction R (G j) (fun k => ¬ B k)) = (algebra R).top := by
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun j => unbounded_witnesses R (G j) (hG j))
  let v (j i k : Nat) := bv_eq (algebra R) (f j i) (natural R k)
  have htotal (j i : Nat) : Regular.iSup (v j i) = Regular.top := by
    have h := (hf j i).1
    rw [omega_mem_eq, algebra_iSup, algebra_top] at h
    exact h
  have hlower (j i k : Nat) (hk : k < i) : v j i k = Regular.bot :=
    small_value_eq_bot R (f j i) i (hf j i).2.1 hk
  obtain ⟨tests, htests, hgood⟩ := hSplit v htotal hlower
  refine ⟨tests, htests, fun B hB j => ⟨?_, ?_⟩⟩
  · exact hits_force_unbounded R (G j) (f j) (fun i => (hf j i).2.1)
      (fun i => (hf j i).2.2) B (fun N => (hgood B hB j N).1)
  · exact hits_force_unbounded R (G j) (f j) (fun i => (hf j i).2.1)
      (fun i => (hf j i).2.2) (fun k => ¬ B k) (fun N => (hgood B hB j N).2)

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

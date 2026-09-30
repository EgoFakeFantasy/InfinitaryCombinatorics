import FIMADModels.OmegaMinimal

/-! Actual intersections, differences, and splitting in the ordinary Boolean
quotient. Infinitude is not silently substituted for bounded unboundedness. -/

set_option autoImplicit false

namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC.Model.Boolean BV_graph TypedModels
universe u
variable {P : Type u} (R : Order P)

theorem quotient_subset_of_top (U : Filter_l (algebra R).toBA_alg)
    (G H : BV_name (Regular R)) (h : subset (algebra R) G H = (algebra R).top) :
    Internal.Subset (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U G) (BooleanQuotient.classOf (algebra R) U H) := by
  intro x
  induction x using Quotient.inductionOn with
  | h X =>
    intro hx
    have ht : U.mem (subset (algebra R) G H) := h ▸ U.top_mem
    exact U.upward (U.meet_mem ht hx) (subset_use (algebra R) G H X)

theorem quotient_restriction_inter (U : Filter_l (algebra R).toBA_alg)
    (G : BV_name (Regular R)) (B : Nat → Prop) :
    Internal.Inter (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (restriction R G B))
      (BooleanQuotient.classOf (algebra R) U G)
      (BooleanQuotient.classOf (algebra R) U (groundReal R B)) := by
  intro x
  induction x using Quotient.inductionOn with
  | h X =>
    change U.mem (bv_mem (algebra R) X (restriction R G B)) ↔ _
    rw [restriction, sep_mem (algebra R) _ _ (stable_elem (algebra R) _)]
    exact UltrafilterTruth.meet_iff (algebra R) U _ _

theorem ground_complement_value (B : Nat → Prop) :
    (algebra R).le (algebra R).top ((algebra R).iInf
      (fun X : BV_name (Regular R) => (algebra R).imp
        (bv_mem (algebra R) X (omega (algebra R)))
        ((algebra R).iff (bv_mem (algebra R) X (groundReal R (fun k => ¬ B k)))
          ((algebra R).neg (bv_mem (algebra R) X (groundReal R B)))))) := by
  classical
  rw [omega_all R _ (stable_iff (algebra R) (stable_elem (algebra R) _)
    (stable_neg (algebra R) (stable_elem (algebra R) _)))]
  apply ((algebra R).le_iInf_iff _ _).mpr
  intro k
  apply ((algebra R).valid_iff_iff _ _).mpr
  unfold groundReal
  rw [real_mem, real_mem]
  by_cases h : B k
  · simp only [h, not_true_eq_false, ↓reduceIte]
    exact ((algebra R).neg_neg (algebra R).bot).symm
  · simp only [h, not_false_eq_true, ↓reduceIte]
    all_goals rfl

theorem quotient_ground_complement (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (B : Nat → Prop) (x : BooleanQuotient.Carrier (algebra R) U)
    (hx : BooleanQuotient.membership (algebra R) U x
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))) :
    BooleanQuotient.membership (algebra R) U x
      (BooleanQuotient.classOf (algebra R) U (groundReal R (fun k => ¬ B k))) ↔
      ¬ BooleanQuotient.membership (algebra R) U x
        (BooleanQuotient.classOf (algebra R) U (groundReal R B)) := by
  induction x using Quotient.inductionOn with
  | h X =>
    have ht := U.upward U.top_mem ((algebra R).le_trans (ground_complement_value R B)
      ((algebra R).iInf_le _ X))
    have hi := U.upward (U.meet_mem ht hx) ((algebra R).imp_elim _ _)
    exact ((UltrafilterTruth.iff_iff (algebra R) U hU _ _).mp hi).trans
      (UltrafilterTruth.neg_iff (algebra R) U hU _)

theorem quotient_restriction_difference (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (G : BV_name (Regular R)) (hG : subset (algebra R) G (omega (algebra R)) = (algebra R).top)
    (B : Nat → Prop) :
    Internal.Difference (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (restriction R G (fun k => ¬ B k)))
      (BooleanQuotient.classOf (algebra R) U G)
      (BooleanQuotient.classOf (algebra R) U (groundReal R B)) := by
  intro x
  rw [quotient_restriction_inter R U G (fun k => ¬ B k) x]
  constructor
  · intro h
    exact ⟨h.1, (quotient_ground_complement R U hU B x
      (quotient_subset_of_top R U G _ hG x h.1)).mp h.2⟩
  · intro h
    exact ⟨h.1, (quotient_ground_complement R U hU B x
      (quotient_subset_of_top R U G _ hG x h.1)).mpr h.2⟩

/-- The graph-name preservation theorem yields actual unbounded intersections
and differences in the ZFC quotient, using its own membership and natural set. -/
theorem quotient_countable_splitting (hSplit : SplittingCertificate R)
    (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (G : Nat → BV_name (Regular R))
    (hsub : ∀ j, subset (algebra R) (G j) (omega (algebra R)) = (algebra R).top)
    (hG : ∀ j, unboundedValue R (G j) = (algebra R).top) :
    ∃ tests : Nat → Nat → Prop, (∀ n, NatUnbounded (tests n)) ∧
      ∀ B, (∀ n, NatSplits B (tests n)) → ∀ j,
        Internal.UnboundedSplit (BooleanQuotient.membership (algebra R) U)
          (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))
          (BooleanQuotient.classOf (algebra R) U (G j))
          (BooleanQuotient.classOf (algebra R) U (groundReal R B)) := by
  obtain ⟨tests, ht, hgood⟩ := split_unbounded_names R hSplit G hG
  refine ⟨tests, ht, fun B hB j => ?_⟩
  exact ⟨BooleanQuotient.classOf (algebra R) U (restriction R (G j) B),
    BooleanQuotient.classOf (algebra R) U (restriction R (G j) (fun k => ¬ B k)),
    quotient_restriction_inter R U (G j) B,
    quotient_restriction_difference R U hU (G j) (hsub j) B,
    quotient_unbounded_of_top R U hU _ (hgood B hB j).1,
    quotient_unbounded_of_top R U hU _ (hgood B hB j).2⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

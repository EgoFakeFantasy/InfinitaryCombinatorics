import FIMADModels.NativeZF
import FIMADModels.FiniteUnbounded
import FIMADModels.QuotientSplitting

/-! The quotient splitting theorem with the manuscript's original infinitude
predicate, obtained through the native ZF model interface. -/
set_option autoImplicit false
namespace InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular
open YesMetaZFC SetTheory YesMetaZFC.Model.Boolean BV_graph TypedModels
universe u
variable {P : Type u} (R : Order P)

/-- No standardness or countable completeness assumption on the ultrafilter. -/
theorem quotient_infinite_iff_unbounded (U : Filter_l (algebra R).toBA_alg)
    (hU : U.Maximal_l) (a : BooleanQuotient.Carrier (algebra R) U)
    (ha : Internal.Subset (BooleanQuotient.membership (algebra R) U) a
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))) :
    Internal.Infinite (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) a ↔
    Internal.Unbounded (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) a :=
  Internal.infinite_iff_unbounded (BooleanQuotient.models_native_zf (algebra R) U hU)
    (quotient_omega R U hU) ha

/-- The unbounded Boolean value computes the original infinitude predicate. -/
theorem quotient_infinite_iff_value (U : Filter_l (algebra R).toBA_alg)
    (hU : U.Maximal_l) (G : BV_name (Regular R))
    (hsub : subset (algebra R) G (omega (algebra R)) = (algebra R).top) :
    Internal.Infinite (BooleanQuotient.membership (algebra R) U)
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R)))
      (BooleanQuotient.classOf (algebra R) U G) ↔ U.mem (unboundedValue R G) :=
  (quotient_infinite_iff_unbounded R U hU _ (quotient_subset_of_top R U _ _ hsub)).trans
    (quotient_unbounded_iff R U hU G)
/-- Actual graph names, with infinitude measured by absence of internal finite injections. -/
theorem quotient_countable_infinite_splitting (hSplit : SplittingCertificate R)
    (U : Filter_l (algebra R).toBA_alg) (hU : U.Maximal_l)
    (G : Nat → BV_name (Regular R))
    (hsub : ∀ j, subset (algebra R) (G j) (omega (algebra R)) = (algebra R).top)
    (hG : ∀ j, unboundedValue R (G j) = (algebra R).top) :
    ∃ tests : Nat → Nat → Prop, (∀ n, NatUnbounded (tests n)) ∧
      ∀ B, (∀ n, NatSplits B (tests n)) → ∀ j,
        ∃ d e, Internal.Inter (BooleanQuotient.membership (algebra R) U) d
            (BooleanQuotient.classOf (algebra R) U (G j))
            (BooleanQuotient.classOf (algebra R) U (groundReal R B)) ∧
          Internal.Difference (BooleanQuotient.membership (algebra R) U) e
            (BooleanQuotient.classOf (algebra R) U (G j))
            (BooleanQuotient.classOf (algebra R) U (groundReal R B)) ∧
          Internal.Infinite (BooleanQuotient.membership (algebra R) U)
            (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) d ∧
          Internal.Infinite (BooleanQuotient.membership (algebra R) U)
            (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) e := by
  obtain ⟨tests, ht, hgood⟩ := quotient_countable_splitting R hSplit U hU G hsub hG
  refine ⟨tests, ht, fun B hB j => ?_⟩
  obtain ⟨d, e, hd, he, hud, hue⟩ := hgood B hB j
  have hds : Internal.Subset (BooleanQuotient.membership (algebra R) U) d
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) :=
    fun x hx => quotient_subset_of_top R U _ _ (hsub j) x ((hd x).mp hx).1
  have hes : Internal.Subset (BooleanQuotient.membership (algebra R) U) e
      (BooleanQuotient.classOf (algebra R) U (omega (algebra R))) :=
    fun x hx => quotient_subset_of_top R U _ _ (hsub j) x ((he x).mp hx).1
  exact ⟨d, e, hd, he, (quotient_infinite_iff_unbounded R U hU d hds).mpr hud,
    (quotient_infinite_iff_unbounded R U hU e hes).mpr hue⟩

end InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular

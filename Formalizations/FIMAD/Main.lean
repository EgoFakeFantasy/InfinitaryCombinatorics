import Formalizations.FIMAD.SeparationCardinal
import Formalizations.FIMAD.Metatheory

namespace InfinitaryCombinatorics.Formalizations.FIMAD

/-- The paper's exact cutoff, retaining the external comparison as an input. -/
theorem finIntersecting_iff_card_lt_of_ap_le_b {A : Set (Set ℕ)} (hA : ADFamily A)
    (ap_le_b : almostDisjointSeparationNumber ≤ boundingNumber)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber) :
    R0.FinIntersecting A ↔ Cardinal.mk A < R0.splittingNumber :=
  finIntersecting_iff_card_lt hA hsep (hsep.trans_le ap_le_b)

end InfinitaryCombinatorics.Formalizations.FIMAD

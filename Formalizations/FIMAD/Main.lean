import Formalizations.FIMAD.SeparationCardinal
import Formalizations.FIMAD.Metatheory
import Formalizations.FIMAD.CHConstruction

namespace InfinitaryCombinatorics.Formalizations.FIMAD

/-- The paper's exact cutoff under its stated hypothesis alone. -/
theorem finIntersecting_iff_card_lt_of_s_lt_ap {A : Set (Set ℕ)} (hA : ADFamily A)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber) :
    R0.FinIntersecting A ↔ Cardinal.mk A < R0.splittingNumber :=
  finIntersecting_iff_card_lt hA hsep
    (hsep.trans_le almostDisjointSeparationNumber_le_boundingNumber)

end InfinitaryCombinatorics.Formalizations.FIMAD

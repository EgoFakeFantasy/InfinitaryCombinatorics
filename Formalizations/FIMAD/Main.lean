import Formalizations.FIMAD.SeparationCardinal
import Formalizations.FIMAD.Metatheory
import Formalizations.FIMAD.CHConstruction
import Formalizations.FIMAD.MemberwiseSemantics
import Formalizations.FIMAD.ModelInterface
import Formalizations.FIMAD.OmegaSplitting
import Formalizations.FIMAD.GeneralConstruction

namespace InfinitaryCombinatorics.Formalizations.FIMAD

/-- The paper's exact cutoff under its stated hypothesis alone. -/
theorem finIntersecting_iff_card_lt_of_s_lt_ap {A : Set (Set ℕ)} (hA : ADFamily A)
    (hsep : R0.splittingNumber < almostDisjointSeparationNumber) :
    R0.FinIntersecting A ↔ Cardinal.mk A < R0.splittingNumber :=
  finIntersecting_iff_card_lt hA hsep
    (hsep.trans_le almostDisjointSeparationNumber_le_boundingNumber)

/-- The known sufficient condition in the paper's consequences section. -/
theorem exists_fi_mad_of_a_lt_s
    (h : InfinitaryCombinatorics.Formalizations.R0.almostDisjointnessNumber <
      R0.splittingNumber) : ExistsFIMAD := by
  obtain ⟨A, hA, hc⟩ := InfinitaryCombinatorics.Formalizations.R0.exists_minimum_mad_nat
  exact ⟨A, hA, R0.finIntersecting_of_card_lt A (hc ▸ h)⟩

end InfinitaryCombinatorics.Formalizations.FIMAD

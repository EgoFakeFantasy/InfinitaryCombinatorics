import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-! Generic proof-theoretic consequence transport. This module does not encode
FI MAD existence as a set-theoretic sentence and does not construct either model. -/
namespace InfinitaryCombinatorics.Formalizations.FIMAD.Metatheory
open YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder
universe u v w
variable {σ : Signature.{u,v,w}} [DecidableEq σ.SortSymbol]

/-- Genuine syntactic independence in the YesMetaZFC derivation calculus. -/
def Independent (T : Theory σ) (φ : Formula σ) : Prop :=
  (¬ Derives T [] φ) ∧ ¬ Derives T [] (Formula.neg φ)

/-- Two consistent one-sentence extensions rule out proofs on either side.
The consistency witnesses remain explicit, substantive inputs. -/
theorem independent_of_consistent_extensions {T : Theory σ} {φ : Formula σ}
    (hφ : Formula.Admissible φ)
    (hpos : Derives.Consistent T [φ])
    (hneg : Derives.Consistent T [Formula.neg φ]) : Independent T φ := by
  constructor
  · intro hp
    have hnot : ¬ Derives T [] (Formula.neg (Formula.neg φ)) :=
      (Derives.cons_cons_iff_m (Formula.Admissible.neg hφ)).mp hneg
    exact hnot (Derives.neg_neg_intro_m hp)
  · exact (Derives.cons_cons_iff_m hφ).mp hpos

/-- Conditional relative-independence schema; not a forcing theorem. -/
theorem relative_independence {T : Theory σ} {φ : Formula σ}
    (hφ : Formula.Admissible φ)
    (positive : Derives.Consistent T [] → Derives.Consistent T [φ])
    (negative : Derives.Consistent T [] → Derives.Consistent T [Formula.neg φ]) :
    Derives.Consistent T [] → Independent T φ :=
  fun h => independent_of_consistent_extensions hφ (positive h) (negative h)

end InfinitaryCombinatorics.Formalizations.FIMAD.Metatheory

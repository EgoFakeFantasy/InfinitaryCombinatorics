# Model interface for FI MAD independence

The following interfaces use the pinned YesMetaZFC dependency. They do not assert that the remaining models have been constructed.

## Checked target

Namespace: `InfinitaryCombinatorics.Formalizations.FIMAD`.

- `Internal.Syntax.sentence` is the depth-indexed closed sentence for infinite FI MAD existence.
- `ModelInterface.existenceSentence` is its pure first-order translation.
- `ModelInterface.zfcTheory` is `Definitional.Project.fo_theory CheckedZFC.Axiom`.
- `Internal.FirstOrderBridge.toFirstOrder M` interprets the single set sort as the whole domain of the membership structure `M`.
- `Internal.FirstOrderBridge.satisfies_fimad_sentence` proves that the first-order sentence means `Internal.ExistsFIMAD M.mem`, for any extensional `M`.

The internal assertion quantifies only over objects in the structure. Its finite sets have internal injections into internal natural numbers. The finite blocks are nonempty and pairwise disjoint, with no uniform bound on size. FI deletes finite restricted traces before testing all finite nonempty collections of retained traces.

The local `CheckedZFC` presentation uses the same eight fixed formulas as the pinned upstream ZFC presentation and reuses its full separation and collection schemas. It reconstructs the fixed formulas' closure certificates with kernel-checked proofs. This avoids the extra native-evaluation axioms introduced by the upstream `sentence!` macro; it does not weaken or change any ZFC axiom formula.

## Required model witnesses

For the positive direction, supply a structure `M` and proofs of:

```lean
ModelInterface.ModelsZFC M
YesMetaZFC.SetTheory.Extensional M
Internal.ExistsFIMAD M.mem
```

For the negative direction, supply a structure `N` and proofs of:

```lean
ModelInterface.ModelsZFC N
YesMetaZFC.SetTheory.Extensional N
¬ Internal.ExistsFIMAD N.mem
```

`ModelsZFC` requires every assignment to satisfy every formula in the actual translated ZFC theory. Positive and negative structures may have different domain universes.

The checked theorems `positive_consistent_of_model` and `negative_consistent_of_model` consume these witnesses using the public `Derives.sound` theorem. `independent_of_models` then proves nonderivability of the actual E sentence and its negation. For a relative-consistency presentation, the model-producing steps must have the appropriate consistency premise and their metatheoretic strength must be recorded.

## Combinatorial inputs ready for internalization

- `exists_fi_mad_of_CH`: the full CH construction on host natural numbers.
- `exists_fi_mad_extension_of_ap_eq_s_eq_continuum`: the complete continuum-length extension of any infinite small AD family.
- `exists_fi_mad_iff_s_eq_continuum_of_ap_eq_continuum`: the exact host equivalence under ap = continuum.
- `no_fi_mad_of_s_lt_ap`: the main exact-hypothesis negative implication on host natural numbers.
- `dowNumber_le_almostDisjointSeparationNumber`: dp <= ap for actual least witness cardinals.
- `splittingNumber_le_omegaSplittingNumber`: s <= s_omega for actual least witness cardinals.
- `consequences_of_bmz_configuration`: from s_omega = aleph_1, dp = c and c = aleph_2, derives s = aleph_1, ap = b = a = c, and no infinite FI MAD.

These are ordinary Lean mathematical theorems. Their interpretation in mathlib's standard set universe is now checked, as detailed below. Transfer into the required CH/BMZ models is still required: `M` satisfying its CH sentence does not supply host CH, and the host `Set Nat` need not be the model's powerset of its natural numbers. The theorem `finIntersecting_iff_memberwise` alone only checks the finite-member reformulation on host sets; the new standard-universe modules provide the additional finite-set and sequence identifications for that specific universe.

The constructible-universe library's concrete CH model is a candidate positive foundation; no toolchain migration or dependency on a dirty local checkout has been made here. The Dow/BMZ forcing construction is still an external mathematical input.

## New public Boolean infrastructure

The isolated `model-integration/` package now uses public YesMetaZFC commit
`a4903d2054085db0b454363a5fb15f1a3e1f9eab` and Lean 4.33.1. Its
`TypedModels.CheckedBooleanZFC.models_zfc` constructs the full ZFC certificate
from the upstream standard Boolean-name construction; ZFC satisfaction is no
longer supplied as a premise at this endpoint. The concrete E formula and its
internal semantics are shared source files across the two packages.

`positive_consistency` requires nontriviality and top Boolean value of E;
`negative_consistency` requires nontriviality and top Boolean value of its
negation. These truth obligations remain unproved. Generic Boolean-name ZFC
satisfaction alone proves neither one. The required CH/BMZ interpretations,
characteristic computations, and transfer into these particular models remain substantive
mathematical formalization tasks. See the separate package README and its
transitive axiom audit for the exact completed boundary.

## Constructed Boolean quotients (30 September update)

The public filter-core branch supplies Tarski ultrafilter extension. The project
now constructs `BooleanQuotient.quotientStructure`, proves representative
independence of membership, proves a truth lemma for every typed formula,
and verifies ZFC and extensionality in the resulting ordinary model.
Quantifiers use the standard-name maximum principle, not an extra completeness
assumption on the ultrafilter.

`BooleanQuotient.model_of_nonzero` constructs both the ultrafilter and the
ordinary model for any sentence with nonzero Boolean value. In particular,
`positive_model_of_nonzero` yields internal E from a nonzero value of E, and
`negative_model_of_not_top` yields internal not-E when that value is not top.
These constructions close the generic Boolean-to-ordinary-model step.
They do not close the remaining CH/BMZ truth computations, transfer into those models,
topological results, or Cohen preservation.

## Exact standard-universe interpretation

`Standard.model` is the actual membership structure on `ZFSet.{u}`.
`Standard.models_zfc` verifies the complete checked theory in this structure,
including every separation and collection schema with arbitrary parameters.
No ZFC-model hypothesis is supplied to that theorem.

`Standard.existsFIMAD_iff` identifies internal E with host `ExistsFIMAD` at every
universe level. The proof constructs both directions of the natural-number,
real, family, and sequence coding. It proves internal finiteness equivalent to
host finiteness, and checks maximality against all internal infinite subsets
of omega. The FI equivalence covers every internal sequence, arbitrarily large
finite blocks, duplicate traces, and every nonempty finite subfamily of
retained infinite traces. `Standard.satisfies_sentence_iff` connects this to
the actual first-order sentence accepted by the YesMetaZFC proof kernel.

The resulting endpoints are:

- `Standard.positive_consistency_of_CH`: host CH implies consistency of ZFC + E.
- `Standard.positive_consistency_of_ap_eq_s_eq_continuum`: the two host cardinal
  equations imply consistency of ZFC + E.
- `Standard.negative_consistency_of_s_lt_ap`: the host strict inequality implies
  consistency of ZFC + not-E.

These are ambient-foundation results with the displayed cardinal hypotheses.
They are not relative consistency from `Con(ZFC)`. In particular, the positive
and negative host hypotheses cannot be assumed simultaneously to manufacture
an independence proof. Establishing the required separate models, or computing
the corresponding Boolean truth values, remains a distinct obligation.

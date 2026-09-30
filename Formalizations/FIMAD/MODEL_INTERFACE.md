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

## Dow forcing: single-step construction and preservation core

`DowForcing.Condition A` follows Dow, *On compact separable radial spaces*,
[Definition 2, p. 426](https://doi.org/10.4153/CMB-1997-050-0).
A condition has a finite stem and a set of forbidden finite stems satisfying
the tail-extension condition. Smaller conditions are stronger. The source
proves centeredness of every stem fiber, hence ccc, and constructs dense sets
for hitting each infinite member of A and avoiding sets orthogonal to A.
`unionStems_weaklySeparates` verifies the resulting separator for a directed
set meeting those requirements; it does not assume or construct a generic model.

The inductive `Reach` predicate and `reach_all` implement the dense-stem
closure argument underlying Lemma 1. `reach_possible_tests` constructs
countable test families by induction on that closure. The common-value argument
uses only finitely many blocking conditions at a time, together with centered
fibers and the tail-extension condition. `simultaneous_tallness_tests` then
handles countably many increasing enumeration decision relations; applying
its conclusion to B and its complement yields `simultaneous_splitting_tests`.
No preservation assertion is a premise of these theorems.

**Remaining BMZ obligations:** finish the internal sequence-name application
described below; prove finite-support iteration preservation and the relevant
ccc/cardinal facts; implement bookkeeping to handle all small orthogonal
families; verify the final cardinal configuration and the E truth value.
The iteration dependence is spelled out in
[BMZ, Theorem 4(3)](https://arxiv.org/pdf/1306.0204v3), which uses Dow's
single-step preservation and the iteration result of Brendle--Hrusak.
The present declarations do not construct the omega-two-length iteration.

### Concrete regular-open truth values and graph names

`PosetRegular.Regular R` consists of downward-closed predicates fixed by
the operation "dense below a condition". The file constructs implication,
intersection, arbitrary suprema, and double negation, proving all required
complete Boolean algebra laws. `condition` is the canonical dense map from
the preorder. Each condition has nonzero value; no injectivity claim is made
before taking the separative quotient.

`DowBoolean` instantiates this construction with the exact Dow order.
`boolean_antichain_countable` proves ccc of the completion. `genericValue A k`
regularizes the set of conditions whose stem contains k. `generic_hits_top`
and `generic_avoids_top` compute the unbounded-hitting and finite-avoidance
values as top, without supplying a generic filter. `boolean_splitting_tests`
applies the earlier preservation argument to total Boolean enumerations:
the hypotheses are supremum-one of the possible values and bottom values
below the enumeration index; monotonicity and dense decisions are derived.

The separate typed package imports the very same `PosetRegular` file.
`PosetRegular.algebra` supplies the actual YesMetaZFC `CB_alg` structure.
`natural_decisions_dense` uses actual `BV_graph.bv_eq` and membership in the
upstream omega graph. `small_value_eq_bot` obtains the lower-value exclusion
from the semantic assertion i belongs to G or i equals G. Distinct ground
naturals have bottom equality value, and `decisions_disjoint` proves uniqueness
of a decided value. `real b`, `real_mem`, and `real_subset_omega` construct an
actual graph name for every Boolean coefficient sequence and verify its exact
natural membership values and top-valued subset-of-omega assertion.

These are checked components of the semantic connection. The main Dow package
and typed graph-name package still use different Lean versions; their final
application is not a single compiled theorem. The specific FI MAD sentence
value is still uncomputed. In particular, the single-step Boolean calculations
do not establish the BMZ model or the independence theorem.

### Unbounded names and the shared splitting certificate

`BooleanEnumeration.lean` now defines the exact shared `SplittingCertificate`
contract, including a Nat-indexed family of unbounded ground tests.
`DowForcing.splittingCertificate` proves it for the actual Dow order, using
`boolean_splitting_tests` and a proved equivalence between set infinitude and
natural-number unboundedness. The same file is imported unchanged by the
typed package; no second contract or countability convention is substituted.

In that package, `unboundedValue G` is the complete Boolean value of
forall X in omega, exists Y in omega, X <= Y and Y in G. Both variables range
over all graph names. `omega_all` and `omega_sup` reduce bounded quantifiers
to ground natural names; `unbounded_eq_tails` proves the precise tail-value
equality. `unbounded_witnesses` applies the maximum principle to construct
actual names f(i) belonging to G and omega, with i <= f(i), all at top value.
Strictly increasing enumerations are unnecessary for the proved Dow argument.

`restriction G B` is an actual separation name for G intersected with the
ground real B. `hits_force_unbounded` translates witness-value hits into
unboundedness of this restriction. `split_unbounded_names` then derives the
countable-name splitting conclusion from the shared certificate, constructing
its own witnesses. Its certificate premise is explicit and is discharged for
Dow by the theorem in the main package; neither package silently imports a
compiled proof from the other Lean version.

The remaining semantic/build work includes checking this final application
in one toolchain and connecting the bounded unboundedness formula with the
original internal finite/infinite predicates. The finite-support iteration,
bookkeeping, cardinal configuration and full FI MAD value remain open.

### Exact object syntax, least omega, and ordinary quotient splitting

`UnboundedSyntax.lean` adds a separately named `Internal.Unbounded` predicate
and its formula to the existing membership language. Its quantifiers range
over the whole carrier. `Internal.Infinite` keeps its original definition:
there is no internal injection into any member of the internal natural set.
Their equivalence for subsets of omega is now proved in the typed package,
as described below; the definition of infinitude is unchanged.

`UnboundedTruth.lean` proves that evaluating this exact formula in the typed
Boolean name model gives `unboundedValue`. `quotient_unbounded_iff` applies
the full formula truth lemma, including both quantifiers, to obtain precisely
`Internal.Unbounded` in the ordinary maximal-filter quotient. It does not
assume that every natural number of that quotient has a standard representative
or that the filter is countably complete.

`OmegaMinimal.lean` verifies the exact existing `OmegaFormula` at top value.
It proves empty-name uniqueness, successor-name uniqueness, membership of
every ground natural in an arbitrary inductive name under the same Boolean
condition, and hence leastness of the omega graph among all inductive names.
`quotient_omega` transfers this to the original `Internal.Omega` predicate.
Thus the natural set in the quotient splitting statement is a proved least
inductive set, not just a designated graph with an unchecked name.

`QuotientSplitting.lean` proves that restriction names give actual intersections
and differences in the quotient membership relation. Its complement argument
covers all internal members of omega. `quotient_countable_splitting` combines
these facts with the shared certificate to produce `Internal.UnboundedSplit`
for the countable collection of top-valued unbounded names. The certificate
remains explicit.

`NativeZF.lean` exposes the quotient through the upstream native ZF API.
`NativeFinite.lean` implements the manuscript's Kuratowski-pair interpretation
and proves `injection_native_iff`, then reuses the upstream inclusion injection.
`FiniteUnbounded.lean` proves `finite_iff_bounded` and `infinite_iff_unbounded`
for every native ZF model and every internal subset of its least inductive set.
The finite-to-bounded direction uses the upstream internal omega induction:
the property quantifies over all internal domains and injection graphs and is
explicitly separated. At a successor, restriction removes the last fiber;
injectivity makes that fiber contain at most one member. This works in
nonstandard models as well.

`InfiniteSplitting.lean` derives `quotient_infinite_iff_value` and
`quotient_countable_infinite_splitting` with the original finiteness semantics.
The latter retains the certificate and top-valued input hypotheses. These
results do not complete the BMZ iteration or its cardinal arithmetic.

To use the upstream native ZF theorems without enlarging the project's axiom
whitelist, the typed package records and verifies a patch replacing only the
eight fixed axiom formulas' native-evaluation closure certificates with kernel
proofs. Its pinned revision is unchanged. See `model-integration/README.md` and
`dependency-patches/manifest.json` there for reproduction and hashes.

## CH source audit

The inspected constructible-universe source at
`7f5a7d03d63d9769172f17350bbe8303996e5b53` declares
`Constructible.Model.lCarrier_models_ZFCCH` and
`FirstOrder.Language.Theory.ZFCCH_isSatisfiable` in
`ConstructibleUniverse/SetTheory/ZFC/Constructible/CHRelativeConsistency.lean`.
Their target is a concrete L-carrier model in Lean's ambient foundation and
mathlib's first-order language. The file explicitly excludes a claim of
parameterization over arbitrary, possibly externally ill-founded ZFC models.
This turn inspected those sources but did not independently build/audit their
full dependency closure or import them into the project.

To use this route for E, the constructible model must be connected to our
exact theory and sentence, and the CH construction must be performed internally
there. `Standard.existsFIMAD_iff` is specific to the full ZFSet universe and
cannot be reused unchanged for the smaller L-carrier. No theorem in the present
development supplies that missing construction. A source theorem name ending
in `RelativeConsistency` does not by itself certify the required interface.

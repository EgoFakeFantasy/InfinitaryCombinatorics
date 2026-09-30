# Typed Boolean-model integration for FI MAD

This separate package uses Lean 4.33.1 and the public YesMetaZFC revision
`a4903d2054085db0b454363a5fb15f1a3e1f9eab` from the public
`codex/set-theory-filter-core` branch (public `main` was still `51c348a` when checked). The main combinatorial package
keeps Lean 4.30.0 and its existing dependency pins.

The source files `InternalSemantics.lean`, `SetTheorySentence.lean`,
`CheckedZFC.lean`, and `PosetRegular.lean` are imported directly from `../Formalizations/FIMAD/`.
There is no copied or second FI MAD definition. The formula closure proofs
compile on both versions; sentence well-scoping is intrinsic in the new kernel.

## Proved endpoints

- `TypedModels.native_semantics`: the typed first-order sentence means exactly
  the internal membership-language assertion of infinite FI MAD existence.
- `TypedModels.value_correct`: its first-order Boolean value equals the
  Project-formula Boolean evaluator on that same formula.
- `TypedModels.CheckedBooleanZFC.models_zfc`: the standard Boolean names
  satisfy the full ZFC theory, for every complete Boolean algebra. This
  reuses the upstream pair, union, power, infinity, foundation, choice,
  separation and collection constructions. No `ModelsZFC` premise is supplied.
- `TypedModels.positive_consistency` and `negative_consistency`: a nontrivial
  Boolean algebra with the corresponding top-valued sentence gives consistency
  of actual ZFC plus that sentence or its negation.

The fixed ZFC formulas use the existing `CheckedZFC` kernel closure proofs.
The upstream ZFC endpoint depends on extra native-evaluation closure certificates;
this adaptation reconstructs its short ZFC verification using the same name
constructions and the kernel-checked formulas. It does not modify the dependency.
See `THIRD_PARTY_NOTICES.md` for attribution of the adapted proof.

## Actual two-valued models

`BooleanQuotient.quotientStructure` is the quotient of standard Boolean names
by equality whose Boolean value belongs to a maximal proper filter. Membership
is proved independent of representatives. `BooleanQuotient.truth` proves the
full truth lemma for all formulas and assignments. The existential case uses
the upstream maximum principle; the universal case uses an attained maximum
for the negated formula. No countable completeness or genericity of the
ultrafilter is assumed.

`BooleanQuotient.model_of_nonzero` uses the new Tarski extension theorem to
construct a maximal proper filter containing a nonzero sentence value. It then
constructs an actual extensional two-valued model satisfying ZFC and that
sentence. ZFC satisfaction and extensionality are proved, not model inputs.

For the actual FI MAD sentence, `positive_model_of_nonzero` requires only
`existenceValue ≠ bot`; `negative_model_of_not_top` requires only
`existenceValue ≠ top`. Their conclusions use `Internal.ExistsFIMAD` in the
constructed model's own membership relation. `consistency_of_nonzero` supplies
the corresponding stronger consistency endpoint. These are constructions
conditional on the indicated Boolean-value hypotheses; those specific values
remain to be established.

## Exact remaining boundary

`FIMADModels/PosetCompletion.lean` constructs an actual `CB_alg` from the shared
regular-open completion of an arbitrary forcing preorder. It proves that an
actual graph name with top-valued membership in omega has dense natural-number
decisions. `FIMADModels/NaturalNames.lean` proves distinctness of ground
natural names, disjointness of incompatible decisions, and exclusion of values
below a semantically forced lower bound. It also constructs `real b`, a graph
name for a subset of omega whose membership values are exactly b.

The main package proves the Dow completion ccc and computes its canonical
separator coefficients and countable splitting tests. Both packages compile
the same regular-open source. Their end-to-end application to arbitrary
internal sequence names is still pending; cross-version compiled artifacts
are not imported or treated as proof certificates.

The Boolean values of FI MAD existence have **not** been computed in a positive
CH model or a negative BMZ model. The public generic name model does not provide
the BMZ iteration, the required characteristic values, or Cohen preservation.
The host combinatorial proofs also need internalization. Consequently this is
not a complete formal independence proof. The newly constructed quotients
must not be presented as verified CH or BMZ models: their required Boolean-value
hypotheses have not yet been established. Ambient Lean consistency
consequences should not be confused with an internally proved ZFC consistency
statement or a relative-consistency theorem over a specified weak metatheory.

## Reproduce

From this directory, with elan installed:

```text
lake update
lake build
lake env lean Audit.lean
```

On Windows, `./verify.ps1` also checks the sources and records exact hashes in
`verification/manifest.json`. `Audit.lean` audits every project declaration,
including transitive dependencies of the Boolean ZFC theorem, Tarski extension,
maximum principle, full quotient truth lemma, and ordinary model construction. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The main repository
has its own independent `../verify.ps1`; run both packages' checks.

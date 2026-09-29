# Typed Boolean-model integration for FI MAD

This separate package uses Lean 4.33.1 and the public YesMetaZFC revision
`51c348a593e41ef9e158d45c69b33d66c432a9b9`. The main combinatorial package
keeps Lean 4.30.0 and its existing dependency pins.

The source files `InternalSemantics.lean`, `SetTheorySentence.lean`, and
`CheckedZFC.lean` are imported directly from `../Formalizations/FIMAD/`.
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

## Exact remaining boundary

The Boolean values of FI MAD existence have **not** been computed in a positive
CH model or a negative BMZ model. The public generic name model does not provide
the BMZ iteration, the required characteristic values, or Cohen preservation.
The host combinatorial proofs also need internalization. Consequently this is
not a complete formal independence proof, and the conditional consistency
endpoints must not be presented as model constructions. Ambient Lean consistency
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
including transitive dependencies of the actual Boolean ZFC theorem. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The main repository
has its own independent `../verify.ps1`; run both packages' checks.

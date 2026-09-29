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
- `no_fi_mad_of_s_lt_ap`: the main exact-hypothesis negative implication on host natural numbers.
- `dowNumber_le_almostDisjointSeparationNumber`: dp <= ap for actual least witness cardinals.
- `splittingNumber_le_omegaSplittingNumber`: s <= s_omega for actual least witness cardinals.
- `consequences_of_bmz_configuration`: from s_omega = aleph_1, dp = c and c = aleph_2, derives s = aleph_1, ap = b = a = c, and no infinite FI MAD.

These are ordinary Lean mathematical theorems. Their internalization is still required: `M` satisfying its CH sentence does not supply host CH, and the host `Set Nat` need not be the model's powerset of its natural numbers. The theorem `finIntersecting_iff_memberwise` checks the finite-member reformulation on host sets, including duplicate traces, but does not itself identify internal finite sets with external ones.

The constructible-universe library's concrete CH model is a candidate positive foundation; no toolchain migration or dependency on a dirty local checkout has been made here. The Dow/BMZ forcing construction is still an external mathematical input.

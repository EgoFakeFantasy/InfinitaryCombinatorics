# Typed Boolean-model integration for FI MAD

This separate package uses Lean 4.33.1 and the public YesMetaZFC revision
`0e91389178caf34fc916ef40f76f84c3f3733714` from public `main`. The main combinatorial package
keeps Lean 4.30.0 and its existing dependency pins.

The source files `InternalSemantics.lean`, `SetTheorySentence.lean`,
`CheckedZFC.lean`, `PosetRegular.lean`, `BooleanEnumeration.lean`, and `UnboundedSyntax.lean` are imported directly from `../Formalizations/FIMAD/`.
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
constructions and the kernel-checked formulas. The native ZF adapters additionally
use the recorded patch `dependency-patches/kernel-checked-axioms.patch` on this
package's private dependency checkout. The eight fixed axiom formulas are
unchanged; only their closure certificates use kernel proofs. The pinned revision
is unchanged, and `prepare-dependencies.ps1` checks both revision and content hashes,
refusing to overwrite unrelated changes.
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

`UnboundedNames.lean` treats the full bounded-name assertion that G has members
arbitrarily high in omega. It proves exact reduction to tail values and uses
the maximum principle to construct natural names f(i) in G above each i.
`SplittingNames.lean` constructs actual separation names for intersection
with a ground real and its complement. `split_unbounded_names` proves the
countable-name splitting conclusion from `SplittingCertificate`, constructing
all witnesses rather than assuming an enumeration.

The main package proves the Dow completion ccc, computes its canonical
separator coefficients, and proves the shared certificate for the exact Dow
order. Both packages compile the same contract and regular-open sources.
The certificate is still an explicit premise of the generic typed adapter;
its Dow instance is verified in the other package. A single-toolchain build
of the final Dow application is pending. The original internal finite/infinite
predicates are connected in the modules below. Cross-version compiled artifacts are
not imported or treated as proof certificates.

`UnboundedTruth.lean` connects the exact shared unboundedness formula to its
Boolean value and to truth in every maximal-filter quotient.
`OmegaMinimal.lean` proves that the omega graph satisfies the original
`OmegaFormula` at top value, including leastness among all inductive names;
`quotient_omega` gives the exact `Internal.Omega` statement in the quotient.
`QuotientSplitting.lean` verifies actual intersections and differences in that
membership relation and proves `quotient_countable_splitting` from the shared
certificate. Its conclusion is `Internal.UnboundedSplit`.

`NativeZF.lean` makes the quotient a native ZF model for the upstream theorem API.
`NativeFinite.lean` realizes the manuscript's actual Kuratowski pair convention
and proves exact equivalence of its injection predicate with the upstream one.
It reuses `ZF.exists_inclusionInjection`. `FiniteUnbounded.lean` reuses
`Structure.IsOmega.induction`, `membershipWellOrder`, `ZF.separation_exists_d`,
and `ZF.exists_restriction` to prove `finite_iff_bounded` and
`infinite_iff_unbounded` in every native ZF model. The induction property is an
explicit first-order schema separated inside omega; no external induction over
possibly nonstandard model naturals is used.

`InfiniteSplitting.lean` applies these results to the ordinary Boolean quotient.
`quotient_infinite_iff_value` connects the original injection-based infinitude to
membership of `unboundedValue` in the ultrafilter, for subset-of-omega names.
`quotient_countable_infinite_splitting` upgrades both intersection and difference
to original internal infinitude. It still requires the shared splitting
certificate and top-valued unbounded input names; it does not compute a splitting
cardinal or supply the BMZ iteration.

The Boolean values of FI MAD existence have **not** been computed in a positive
CH model or a negative BMZ model. The public generic name model does not provide
the BMZ iteration, the required characteristic values, or Cohen preservation.
The host combinatorial proofs also need internalization. Consequently this is
not a complete formal independence proof. The newly constructed quotients
must not be presented as verified CH or BMZ models: their required Boolean-value
hypotheses have not yet been established. Ambient Lean consistency
consequences should not be confused with an internally proved ZFC consistency
statement or a relative-consistency theorem over a specified weak metatheory.

## Object-theory endpoints

`ObjectTheory.lean` constructs closed pure-membership sentences and proves
`derives_finite_iff_bounded` and `derives_infinite_iff_unbounded` in the original
`Project.Derives ZF` interface. `ForcingFinite.lean` proves `derives_finite_bridge`:
the manuscript's original finite-injection formula is equivalent to the new
forcing library's finite-set formula. The Kuratowski graph coding is identical.

`Iteration.lean` constructs the actual name-level successor CCC specification
and proves `derives_system_ccc` in original ZFC. `IterationSchema.lean` proves
`derives_iteration_exists` for every original `BinarySchema` successor rule.
Its closed object sentence includes the rule's totality, uniqueness, stage
links, finite support and actual forced-CCC hypotheses. Its conclusion constructs
the whole internal recursive stage system and proves CCC at every stage.
The rule's external finite parameter index stays external; all object parameters
are universally quantified. No specification is introduced as an axiom.

These endpoints use the original strong-completeness theorem for the countable
pure-membership signature. The typed ZF/ZFC axioms and native model reduct are
matched explicitly. Completeness needs universe-zero models for this signature;
the native semantic lemmas hold at every universe and therefore cover that range.
Lean's classical metatheory is part of proof certification; choice is not added
to the object ZF theory. No external well-foundedness or standard omega is used.

The specific internal Dow successor rule, BMZ bookkeeping and splitting
preservation, and the internal CH construction of FI MAD existence are still
unproved. The generic iteration schema is not a formal BMZ configuration or a
complete independence proof.
## Reproduce

From this directory, with elan installed:

```text
lake update
pwsh -File prepare-dependencies.ps1
lake build
lake env lean Audit.lean
```

On Windows, `./verify.ps1` also checks the sources and records exact hashes in
`verification/manifest.json`. `Audit.lean` audits every project declaration,
including transitive dependencies of the Boolean ZFC theorem, Tarski extension,
maximum principle, full quotient truth lemma, and ordinary model construction. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The main repository
has its own independent `../verify.ps1`; run both packages' checks.

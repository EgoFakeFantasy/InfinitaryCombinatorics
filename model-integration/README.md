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
CH model or a negative BMZ model. The public library provides generic finite-support
iteration, but its BMZ-specific rule, characteristic values and splitting
preservation are not yet instantiated here.
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

`DowInternal.lean` proves `derives_same_stem_merge` in original ZF for actual
forbidden-stem conditions. `FiniteStems.lean` proves
`derives_countable_finite_stems` in original ZFC. The finite enumeration is
obtained by internal finite-set insertion induction and actual sequence graphs;
the injection numbers all internal finite subsets, not merely externally finite
sets. This countability proof uses ZFC's internal fiber selection explicitly.

`DowPoset.lean` proves `derives_dow_poset_ccc` in original ZFC. Its existential
object sentence constructs the exact Kuratowski-coded carrier, the prescribed
strengthening relation, a maximum condition, and the internal CCC proof. The
forbidden coordinate may be any internal set of finite stems. The carrier and
relation specifications are conclusions rather than supplied poset hypotheses.
The CCC argument constructs an internal injection from every antichain into
the finite-stem space using the same-stem merge. The name-level tests and
conditional forced-splitting endpoints below are now proved in this same
package; this does not yet supply the BMZ successor rule or limit argument.

The specific internal Dow successor rule, BMZ bookkeeping and preservation
through the full iteration, and the internal CH construction of FI MAD existence
are still unproved. The generic iteration schema is not a formal BMZ
configuration or a complete independence proof.

## Internal Dow dense sets, generic real and preservation tools

`DowDense`, `DowAvoid`, and `DowSeparator` prove original `Project.Derives ZF`
endpoints for the infinite-hitting and finite-avoidance extensions and the
directed-set separator theorem. The last theorem explicitly assumes a directed
internal set meeting the requirements; it does not assert such a set exists in
the ground model.

`DowGeneric` constructs an actual internal weighted name for the union of
generic stems, proves its exact quotient membership equation, and uses separated
internal dense sets to prove the generic meets both kinds of requirement.
`DowExtension.dow_extension_exists` constructs a genuine ZFC extension of an
enumerated ground model, with an injective, member-covering canonical embedding
and a real weakly separating the images of the specified orthogonal families.
Its finite and infinite intersection assertions use the extension's original
injection-based definitions. No external well-foundedness or standard omega is
assumed. This model construction is an intermediate semantic result; it does
not by itself prove the final independence statement in the original kernel.

`DowAmalgamation` proves original ZF finite same-stem amalgamation by internal
finite-set insertion induction. `DowReach` constructs the internal least
dense-stem closure and proves that every finite stem belongs to it, in original
ZF. `DowPossible` and `DowFiniteTail` prove original ZFC finite impossible-value
elimination and the finite-tail possible-value argument. Selection uses a
model-internal graph obtained from collection and choice, and its internally
finite range is amalgamated. These are preservation tools for an actual
internal decision relation.

`DowTests`, `DowTestAssembly` and `DowTestExistence` then construct the countable
test families: `derives_countable_tests` is an original ZFC proof. It assumes
an actual internal decision relation with monotonicity and natural-valued
decisions on a dense set, and constructs tests for every internal finite stem.
All selections, test families, countable unions and tail-value sets belong to
the model. The closure step uses collection/choice and actual internal graphs;
the least dense-stem closure supplies the induction principle.

`DowValueTails`, `DowTallTests` and `DowTallness` construct tests simultaneously
for all internal finite stems and natural bounds. `derives_tail_tests` and
`derives_tall_tests` are original ZFC proofs. The tail restriction is to internal
natural values, and the restricted decision relation, its dense set, the
selected families and every possible-value set are actual model sets.

`CheckDecisions` reuses the public check-name member reflection and forced
equality congruence to extract canonical ground witnesses from bounded forcing
quantifiers. `DowNameTests` constructs the internal member-decision graph of an
actual forcing name and proves the monotonicity and unbounded-density hypotheses
from its translated unbounded-name formula. `DowNameTheorem.derives_name_tall_tests`
puts this whole application in the original ZFC kernel; it does not take an
abstract decision-density certificate as input.

`DowNameFamily` and `DowNameFamilyTheorem` construct one internal countable test
family for every internally countable set of names that are globally forced
unbounded. The selected relation/test pairs are bounded inside powersets and
chosen by an actual internal function graph. `derives_countable_name_tests` is
an original ZFC proof. `DowNameExtension` and `DowNameSplitting` then verify
infinite intersection and both sides of splitting in the actual generic quotient,
using its own omega and original injection-based infinitude.

`DowSplittingSyntax` encodes that same splitting predicate in the original
language. `DowSplittingForcing.derives_forced_splitting` proves in original ZF
that a ground set splitting the constructed tests forces splitting of the
corresponding real name. It uses the public finite-parameter generic criterion,
whose model universe and original ZF background match the proved semantic
lemma; it does not require an externally countable or well-founded ground model.
`DowOmegaSplitting.derives_preservation_for_countable_names` proves in original
ZFC that an internal omega-splitting family supplies one ground splitter for
every name in the given countable family.

`DowInfiniteNames.derives_infinite_name_unbounded` proves the connection from
the original injection-based infinitude to the exact name-unboundedness formula
in original ZF. `globally_forced_infinite_unbounded` combines the public
canonical omega-name theorem with local forcing implication elimination;
`countable_infinite_name_tests_exists` therefore accepts names globally forced
to be infinite subsets of omega in the manuscript's original sense.

`NameNormalization` constructs actual globally infinite real names that agree
with the inputs wherever those inputs are forced infinite reals. Its original
ZFC derivation uses the public original-formula maximum principle.
`NameNormalizationFamily` makes the choices an actual internal graph and
countable image. `DowConditionalTheorem` consequently removes global infinitude
from the input-name hypotheses in an original ZFC preservation theorem.

`CountableRealEnumeration.derives_countable_real_enumeration` proves in original
ZF that every internal countable family of infinite reals has an internal
omega-function covering it, with omega at unused indices. `FunctionValueNames`
and `FunctionCanonicalValues` apply the original maximum principle at canonical
indices. `ExtensionFamilyNames` then covers **every internally countable family
of infinite reals in an actual generic quotient** by values of an internal
countable ground set of names. No external sequence of representatives is used.

`DowExtensionPreservation` proves omega-splitting for the canonical image of
the original family in every native Dow generic quotient, first restricting
arbitrary test families to their infinite members. Finally,
`DowPreservationTheorem.derives_dow_omega_splitting_preservation` is an original
`Project.Derives ZFC` proof of the corresponding genuine forcing assertion.
The public finite-parameter countable reflection preserves **ZFC**, including
choice, and the public countable forcing criterion consumes the quotient
proof. There is no extra abstract preservation or name-coding hypothesis.

Single-step omega-splitting preservation is therefore complete. The BMZ
successor policy, iteration limit preservation, bookkeeping and final cardinal
configuration, native CH construction, native FI obstruction and final relative
consistency proof remain open. The full independence flag remains false.

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

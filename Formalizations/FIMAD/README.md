# FI MAD: finite-trace coding and the independence argument

Entry point: `Formalizations.FIMAD.Main`.

This project accompanies Haoxuan Ye, *Weak separation and finite-trace coding: independence of infinite fin-intersecting MAD families* (30 September 2026). The English manuscript is in `paper/fi-mad-independence/main.tex`.

## Mathematical content

The coding lemma simultaneously realizes prescribed traces modulo finite from countably many weak intersection tests on a family of size less than b. A direct binary-tree proof establishes ap <= b. Consequently the exact cutoff and nonexistence theorem now require **only s < ap**, as in the paper. Neither ap <= b nor s < b is an additional input to these public theorems. The diagonal comparison b <= a is also proved.

The positive direction is now proved as well: **CH implies an infinite FI MAD family of size aleph_1**. The construction uses the actual first uncountable ordinal, carries out the well-founded recursion, proves maximality against every infinite subset of Nat, and verifies FI against every fin-sequence. Its only hypothesis is the usual cardinal equation for CH. The extension and preservation lemmas are proved, not supplied as assumptions.

The stronger positive theorem is also checked: **ap = s = continuum implies FI MAD existence**, and every infinite AD family of size below the continuum extends to one. This uses a proved AD refinement below b, positive-set extraction below a, simultaneous positive extension below ap, and recursion along the initial ordinal of the continuum. The equivalence **E iff s = continuum under ap = continuum** is therefore checked in full on host sets.

Here ap and b are actual least cardinals of the respective witness classes, not arbitrary parameters. The nonemptiness of both classes is proved. AD families may be finite; `MAD` requires infinitely many members. Blocks are nonempty and finite with no uniform size bound. All infinite retained traces participate in centeredness.

## Coverage and external inputs

| Paper statement | Checked Lean declaration | Exact boundary |
| --- | --- | --- |
| Uniform finite-trace coding | `uniform_trace_coding`, `bounding_of_card_lt` | Fully checked on sets of natural numbers; each member has its own eventual threshold |
| Nonempty witness class defining ap | `nonseparableCardinals_nonempty`, `exists_minimum_nonseparable` | Fully checked using the existing continuum-sized MAD construction and Cantor's theorem |
| b <= a | `boundingNumber_le_almostDisjointnessNumber` | Fully checked, not assumed |
| ap <= b | `almostDisjointSeparationNumber_le_boundingNumber` | Fully checked by a direct branch argument; no literature theorem assumed |
| Arbitrary labels below ap | `arbitrary_labels_below_ap` | Fully checked under size(A) < ap; empty positive fibers handled |
| Every large AD candidate fails FI | `not_finIntersecting_of_large` | Fully checked under s < ap and s < b |
| Exact cutoff FI(A) iff size(A) < s | `finIntersecting_iff_card_lt` | Fully checked under both inequalities; lower bound reuses the library |
| Main paper cutoff from s < ap | `finIntersecting_iff_card_lt_of_s_lt_ap` | Fully checked under the paper's exact hypothesis |
| No infinite FI MAD | `no_fi_mad_of_s_lt_ap_and_b` | Fully checked under both inequalities |
| No infinite FI MAD from s < ap | `no_fi_mad_of_s_lt_ap` | Fully checked under the paper's exact hypothesis |
| E implies ap <= s | `fi_mad_implies_ap_le_s` | Fully checked, with no additional hypotheses |
| Countable positive extension | `countable_positive_extension` | Meets every positive requirement infinitely; almost disjoint from all old members |
| Ideal block cover | `ideal_block_cover_witness` | Produces a witness for the entire AD family |
| CH positive recursion | `exists_fi_mad_of_CH`, `exists_fi_mad_size_aleph_one_of_CH` | Fully checked on Nat under CH, including recursion, maximality, FI, and cardinality |
| Two consistent extensions imply syntactic independence | `Metatheory.relative_independence` | Generic YesMetaZFC proof-calculus theorem, **not instantiated for E or ZFC** |
| Memberwise FI versus centered retained traces | `finIntersecting_iff_memberwise` | Full equivalence, including duplicate traces; no AD assumption |
| Actual membership-language sentence for E | `Internal.Syntax.sentence_semantics`, `sentence_is_firstOrder` | Closed, well-formed sentence; internal finite sets, functions, MAD and FI |
| Semantics in the public first-order proof kernel | `Internal.FirstOrderBridge.satisfies_fimad_sentence` | Translation preserves the internal meaning in every extensional membership structure |
| Actual ZFC/E model-to-independence interface | `ModelInterface.independent_of_models` | Actual positive and negative ZFC models are still explicit inputs; neither model is constructed here |
| dp and its comparison with ap | `exists_minimum_dow`, `dowNumber_le_almostDisjointSeparationNumber` | Actual orthogonal-family witness class, proved nonempty |
| Simultaneous splitting and s <= s_omega | `exists_simultaneous_splitter`, `splittingNumber_le_omegaSplittingNumber` | Actual least witness cardinal; existence and the continuum upper bound are proved |
| Consequences of the BMZ configuration | `consequences_of_bmz_configuration` | Derives the paper's characteristic values and no FI MAD from the stated configuration; does not force the configuration |
| The known a < s sufficient condition | `exists_fi_mad_of_a_lt_s` | Reuses a minimum MAD family and the small-family FI theorem |
| BMZ/Dow relative consistency | No Lean declaration | Single-step poset and decision-relation preservation now checked; full forcing-name semantics and iteration not yet formalized |
| Dow's actual single-step poset | `DowForcing.Condition`, `sigma_centered`, `antichain_countable` | Definition 2, forbidden finite stems; not the simpler Solovay forcing |
| Dense requirements and weak separation | `DowForcing.hit_dense`, `avoid_dense`, `unionStems_weaklySeparates` | Dense sets are constructed; a directed set meeting them is an explicit input |
| Dense-stem closure | `DowForcing.reach_all` | The well-founded closure argument underlying Dow's Lemma 1 |
| Countable tallness and splitting tests | `DowForcing.simultaneous_tallness_tests`, `simultaneous_splitting_tests` | Countable witnesses constructed from monotone dense decision relations; real forcing-name interpretation and iteration still needed |
| Relative consistency of CH | No Lean declaration | CH as a cardinal hypothesis is not a proof of its relative consistency over ZFC |
| Exact semantics in the standard set universe | `Standard.existsFIMAD_iff`, `Standard.satisfies_sentence_iff` | All subsets, arbitrary families, sequences, and retained traces; not a transfer to arbitrary models |
| Standard universe satisfies checked ZFC | `Standard.models_zfc` | Concrete membership structure, full separation and collection |
| Consistency under host cardinal hypotheses | `Standard.positive_consistency_of_CH`, `Standard.negative_consistency_of_s_lt_ap` | Actual model plus soundness; host hypotheses remain inputs |
| Transfer into CH and BMZ models | No Lean declaration | Standard-universe semantics does not supply the required relative consistency constructions |
| AD refinement below b | `ad_refinement_below_b` | Actual infinite subsets, indexed pairwise almost disjointness; derived from uniform block coding |
| Positive extraction and simultaneous extension below ap | `positive_subset_below_a`, `small_positive_extension` | Full arbitrary small families, not only countable stages |
| Positive theorem under ap = s = continuum | `exists_fi_mad_extension_of_ap_eq_s_eq_continuum`, `exists_fi_mad_of_ap_eq_s_eq_continuum` | Fully checked; extends any infinite AD family of size less than the continuum |
| Under ap = continuum, E iff s = continuum | `exists_fi_mad_iff_s_eq_continuum_of_ap_eq_continuum` | Fully checked on host sets |
| Typed sentence and standard Boolean ZFC model | `TypedModels.native_semantics`, `value_correct`, `CheckedBooleanZFC.models_zfc` in `model-integration/` | Separate Lean 4.33.1 build, sharing the same sentence source; generic ZFC satisfaction is proved |
| Boolean consistency endpoints for E and its negation | `TypedModels.positive_consistency`, `negative_consistency` | The original top-valued endpoints are retained; specific truth values remain unproved |
| Ordinary quotient and full truth lemma | `TypedModels.BooleanQuotient.truth`, `models_zfc`, `extensional` | Actual quotient by Boolean equality modulo a maximal proper filter; both quantifiers checked via attained maxima |
| Actual ordinary models from Boolean values | `TypedModels.positive_model_of_nonzero`, `negative_model_of_not_top` | The filter and model are constructed; only the specific nonzero/non-top value remains a premise |
| Consistency from nonzero value | `TypedModels.consistency_of_nonzero` | Stronger than the original top-valued endpoint; does not compute the required CH/BMZ truth values |
| Topological corollaries and Cohen preservation | No Lean declaration | Paper deductions with named published inputs; not machine checked |

**The repository does not claim a complete formalization of the ZFC independence theorem.** The object-language encoding and its exact meaning in mathlib's standard well-founded set universe are checked. That concrete universe satisfies the checked ZFC theory, so host CH gives consistency of ZFC + E and host s < ap gives consistency of ZFC + not-E. Neither host cardinal hypothesis is established by these semantic results. Transfer into the required CH/BMZ models and the specific Boolean-value computations remain open. Ordinary ZFC models are also constructed from nonzero values, but the required specific values have not been proved. No placeholders or new logical assumptions are introduced as declarations to bypass these obligations. See [MODEL_INTERFACE.md](MODEL_INTERFACE.md) for the precise model contracts.

## Module guide

- `TraceCoding.lean`: eventual domination/equality and the block construction.
- `Obstruction.lean`: cardinal definitions, weak separation, paired splitting labels, finite-error contradiction.
- `SeparationBounding.lean`: ap <= b, including countable domination and the binary-branch proof.
- `Nonexistence.lean`: diagonal nonmaximality, b <= a, no-FI-MAD consequences, arbitrary labels.
- `SeparationCardinal.lean`: existence of a minimum nonseparable AD cardinal.
- `PositiveExtension.lean`: simultaneous positive-set hitting and ideal maximality criterion.
- `IdealCover.lean`: homogeneous thinning, ideal cover witness, and the block-to-trace step.
- `CHConstruction.lean`: actual ordinal recursion and complete CH existence theorem.
- `SmallPositiveExtension.lean`: indexed AD refinement below b, extraction below a, and positive extension below ap.
- `GeneralConstruction.lean`: full continuum-length construction under ap = s = c, and E iff s = c when ap = c.
- `Metatheory.lean`: genuine `Derives` and `Derives.Consistent` from YesMetaZFC.
- `InternalSemantics.lean`, `SetTheorySentence.lean`: internal membership meanings and the closed E sentence, with structural semantic proofs.
- `FirstOrderSemantics.lean`: semantics-preserving translation to the public first-order proof kernel.
- `MemberwiseSemantics.lean`: finite-member versus finite-retained-trace equivalence.
- `CheckedZFC.lean`: the upstream ZFC formulas with kernel-checked closure certificates; full separation and collection schemas reused unchanged.
- `ModelInterface.lean`: actual ZFC/E model contracts and soundness consequences.
- `StandardSemantics.lean`: standard omega, Kuratowski pairs, function graphs, and equivalence of internal and external finiteness.
- `StandardCoding.lean`: all real/family codes and the exact AD/MAD equivalences.
- `StandardSequences.lean`: coding and decoding arbitrary finite-block sequences, restricted and common traces.
- `StandardTransfer.lean`: FI and the full internal E sentence agree with the host predicates, at every universe level.
- `StandardModel.lean`: concrete standard model of full checked ZFC, exact first-order meaning, and consistency from the stated host cardinal hypotheses.
- `DowCardinal.lean`, `OmegaSplitting.lean`: actual dp and s_omega, their basic comparisons, and the consequences of the BMZ configuration.
- `DowForcing.lean`: the actual forbidden-stem poset, centered fibers, ccc, dense hitting/avoidance, directed-set separator, and dense-stem closure.
- `DowPossibleValues.lean`: common possible values and the countable test-family induction for Dow's preservation argument.
- `DowTallness.lean`: simultaneous countable tallness/splitting tests for explicit monotone dense natural-number decision relations.
- `PosetRegular.lean`: regular lower sets of any forcing preorder, complete Boolean operations, nonzero canonical condition values, and dense decision semantics; shared unchanged by both toolchains.
- `DowBoolean.lean`: the actual Dow completion is ccc; canonical union-of-stems coefficients have top-valued unbounded hitting and finite avoidance; total Boolean enumerations have countable splitting tests without an assumed decision-density premise.
- `BooleanEnumeration.lean`, `DowCertificate.lean`: shared countable Boolean splitting contract and its proof for the exact Dow order. The typed `SplittingNames` adapter consumes this same source-level contract.
- `UnboundedSyntax.lean`: unboundedness and unbounded splitting in the original membership language, with a checked formula; the original injection-based definition of infinitude is retained.
- `Main.lean`: public entry point and paper-facing cutoff under s < ap alone.

Reused foundations: `InfinitaryCombinatorics.FinIntersection`, `InfinitaryCombinatorics.Characteristics`, and the existing R0 countable-completion and uniform-MAD modules. The protected `R0/` snapshot is unchanged.

## Reproduction

Install the pinned Lean toolchain using elan, then run from the repository root:

```text
lake update
lake exe cache get
lake build
lake env lean CheckFormalizations.lean
lake env lean Audit.lean
```

On Windows, `./verify.ps1` runs the complete source scan, umbrella coverage check, protected snapshot check, build, statement checks, and transitive logical-assumption audit. The current evidence is `verification/manifest.json` and its companion logs. Standard permitted Lean foundations are `propext`, `Classical.choice`, and `Quot.sound`.

Pinned dependencies: Lean 4.30.0; mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; YesMetaZFC `bae4fcc31b07b505986b11c6c2f13965ae6cd46d`. YesMetaZFC is a Git dependency; uncommitted files in a developer's separate checkout are not used.

The isolated [typed model integration](../../model-integration/README.md) pins Lean 4.33.1 and YesMetaZFC `0e91389178caf34fc916ef40f76f84c3f3733714`. It uses the same `InternalSemantics`, `SetTheorySentence`, `CheckedZFC`, and `PosetRegular` sources and has its own `verify.ps1` and manifest. Its `PosetCompletion` and `NaturalNames` modules construct the YesMetaZFC algebra, prove dense decisions for actual natural-number graph names, and realize any Boolean membership coefficients as a name for a subset of omega. It does not change the main package pins. The Dow combinatorics and the typed graph-name application are still compiled in separate packages; there is not yet a single checked theorem applying the former to arbitrary internal sequence names in the latter. Both audits permit only the same three foundational axioms.

The isolated package now also proves original-kernel object-theory endpoints
for finite/infinite boundedness, the exact forcing finiteness bridge, generic
finite-support CCC preservation and iteration existence. Its `DowInternal`,
`FiniteStems`, and `DowPoset` modules internalize the exact forbidden-stem
conditions. They construct the actual carrier, strengthening relation and
maximum condition and prove the CCC in original `Project.Derives ZFC`.
These results do not yet instantiate the name-level Dow successor rule, prove
BMZ splitting preservation or bookkeeping, or construct internal FI MAD from CH.

## Sources and provenance

- Corral and Rodrigues, *Fin-intersecting MAD families*, Filomat 38(7), 2024, 2563-2578, DOI: 10.2298/FIL2407563C.
- Banakh, Machura and Zdomskyy, *On critical cardinalities related to Q-sets*, arXiv:1306.0204v3, Theorem 2 and Theorem 4(3).
- Corral and Rodrigues, *New examples of MAD families with pseudocompact hyperspaces*, arXiv:2309.03405v2, Theorem 5 and Question 7.

The manuscript and Lean development were prepared with generative AI assistance, including GPT-6 Astra. No independent expert review is claimed. Kernel verification covers only the exact checked statements and their explicit assumptions; it does not certify priority or the external literature.

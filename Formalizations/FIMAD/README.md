# FI MAD: finite-trace coding and the independence argument

Entry point: `Formalizations.FIMAD.Main`.

This project accompanies Haoxuan Ye, *Weak separation and finite-trace coding: independence of infinite fin-intersecting MAD families* (29 September 2026). The English manuscript is in `paper/fi-mad-independence/main.tex`.

## Mathematical content

The coding lemma simultaneously realizes prescribed traces modulo finite from countably many weak intersection tests on a family of size less than b. A direct binary-tree proof establishes ap <= b. Consequently the exact cutoff and nonexistence theorem now require **only s < ap**, as in the paper. Neither ap <= b nor s < b is an additional input to these public theorems. The diagonal comparison b <= a is also proved.

The positive direction is now proved as well: **CH implies an infinite FI MAD family of size aleph_1**. The construction uses the actual first uncountable ordinal, carries out the well-founded recursion, proves maximality against every infinite subset of Nat, and verifies FI against every fin-sequence. Its only hypothesis is the usual cardinal equation for CH. The extension and preservation lemmas are proved, not supplied as assumptions.

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
| BMZ/Dow relative consistency | No Lean declaration | Cited published result; forcing not formalized |
| Relative consistency of CH | No Lean declaration | CH as a cardinal hypothesis is not a proof of its relative consistency over ZFC |
| Transfer of host Nat proofs into ZFC models | No Lean declaration | The sentence and its internal semantics are checked, but the host CH and cutoff proofs are not yet internalized |
| Positive theorem under ap = s = continuum | No Lean declaration | The CH theorem does not establish this stronger published result |
| Topological corollaries and Cohen preservation | No Lean declaration | Paper deductions with named published inputs; not machine checked |

**The repository does not claim a complete formalization of the ZFC independence theorem.** The object-language encoding is now implemented, together with its semantic interpretation and a concrete ZFC/E model interface. The transfer of the host combinatorial proofs into models and the actual positive and negative model constructions remain open formalization obligations. No placeholders or new logical assumptions are introduced as declarations to bypass these obligations. See [MODEL_INTERFACE.md](MODEL_INTERFACE.md) for the precise model contracts.

## Module guide

- `TraceCoding.lean`: eventual domination/equality and the block construction.
- `Obstruction.lean`: cardinal definitions, weak separation, paired splitting labels, finite-error contradiction.
- `SeparationBounding.lean`: ap <= b, including countable domination and the binary-branch proof.
- `Nonexistence.lean`: diagonal nonmaximality, b <= a, no-FI-MAD consequences, arbitrary labels.
- `SeparationCardinal.lean`: existence of a minimum nonseparable AD cardinal.
- `PositiveExtension.lean`: simultaneous positive-set hitting and ideal maximality criterion.
- `IdealCover.lean`: homogeneous thinning, ideal cover witness, and the block-to-trace step.
- `CHConstruction.lean`: actual ordinal recursion and complete CH existence theorem.
- `Metatheory.lean`: genuine `Derives` and `Derives.Consistent` from YesMetaZFC.
- `InternalSemantics.lean`, `SetTheorySentence.lean`: internal membership meanings and the closed E sentence, with structural semantic proofs.
- `FirstOrderSemantics.lean`: semantics-preserving translation to the public first-order proof kernel.
- `MemberwiseSemantics.lean`: finite-member versus finite-retained-trace equivalence.
- `CheckedZFC.lean`: the upstream ZFC formulas with kernel-checked closure certificates; full separation and collection schemas reused unchanged.
- `ModelInterface.lean`: actual ZFC/E model contracts and soundness consequences.
- `DowCardinal.lean`, `OmegaSplitting.lean`: actual dp and s_omega, their basic comparisons, and the consequences of the BMZ configuration.
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

## Sources and provenance

- Corral and Rodrigues, *Fin-intersecting MAD families*, Filomat 38(7), 2024, 2563-2578, DOI: 10.2298/FIL2407563C.
- Banakh, Machura and Zdomskyy, *On critical cardinalities related to Q-sets*, arXiv:1306.0204v3, Theorem 2 and Theorem 4(3).
- Corral and Rodrigues, *New examples of MAD families with pseudocompact hyperspaces*, arXiv:2309.03405v2, Theorem 5 and Question 7.

The manuscript and Lean development were prepared with generative AI assistance, including GPT-6 Astra. No independent expert review is claimed. Kernel verification covers only the exact checked statements and their explicit assumptions; it does not certify priority or the external literature.

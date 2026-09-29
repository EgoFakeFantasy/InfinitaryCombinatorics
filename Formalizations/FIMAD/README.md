# FI MAD: finite-trace coding and the independence argument

Entry point: `Formalizations.FIMAD.Main`.

This project accompanies Haoxuan Ye, *Weak separation and finite-trace coding: independence of infinite fin-intersecting MAD families* (29 September 2026). The English manuscript is in `paper/fi-mad-independence/main.tex`.

## Mathematical content

The new coding lemma simultaneously realizes prescribed traces modulo finite from countably many weak intersection tests on a family of size less than b. It gives a fixed blocking fin-sequence for **every** AD family of size at least s when s < ap and s < b. A diagonal proof of b <= a then excludes every infinite FI MAD family under these two inequalities.

Here ap and b are actual least cardinals of the respective witness classes, not arbitrary parameters. The nonemptiness of both classes is proved. AD families may be finite; `MAD` requires infinitely many members. Blocks are nonempty and finite with no uniform size bound. All infinite retained traces participate in centeredness.

## Coverage and external inputs

| Paper statement | Checked Lean declaration | Exact boundary |
| --- | --- | --- |
| Uniform finite-trace coding | `uniform_trace_coding`, `bounding_of_card_lt` | Fully checked on sets of natural numbers; each member has its own eventual threshold |
| Nonempty witness class defining ap | `nonseparableCardinals_nonempty`, `exists_minimum_nonseparable` | Fully checked using the existing continuum-sized MAD construction and Cantor's theorem |
| b <= a | `boundingNumber_le_almostDisjointnessNumber` | Fully checked, not assumed |
| Arbitrary labels below ap | `arbitrary_labels_below_ap` | Explicit additional hypothesis ap <= b; empty positive fibers handled |
| Every large AD candidate fails FI | `not_finIntersecting_of_large` | Fully checked under s < ap and s < b |
| Exact cutoff FI(A) iff size(A) < s | `finIntersecting_iff_card_lt` | Fully checked under both inequalities; lower bound reuses the library |
| Main paper cutoff from s < ap | `finIntersecting_iff_card_lt_of_ap_le_b` | Explicit literature input ap <= b |
| No infinite FI MAD | `no_fi_mad_of_s_lt_ap_and_b` | Fully checked under both inequalities |
| No infinite FI MAD from s < ap | `no_fi_mad_of_s_lt_ap` | Explicit literature input ap <= b |
| E implies ap <= s | `fi_mad_implies_ap_le_s` | Explicit literature input ap <= b |
| Two consistent extensions imply syntactic independence | `Metatheory.relative_independence` | Generic YesMetaZFC proof-calculus theorem, **not instantiated for E or ZFC** |
| CH positive recursion | No Lean declaration | Complete paper proof; not machine checked |
| BMZ/Dow relative consistency | No Lean declaration | Cited published result; forcing not formalized |
| Actual ZFC sentence for E and semantic bridge | No Lean declaration | Not implemented |
| Topological corollaries and Cohen preservation | No Lean declaration | Paper deductions with named published inputs; not machine checked |

**The repository does not claim a complete formalization of the ZFC independence theorem.** A conditional implication and a generic consistency schema do not discharge the missing model constructions or the object-language encoding. No placeholders or new logical assumptions are introduced as declarations to bypass these obligations.

## Module guide

- `TraceCoding.lean`: eventual domination/equality and the block construction.
- `Obstruction.lean`: cardinal definitions, weak separation, paired splitting labels, finite-error contradiction.
- `Nonexistence.lean`: diagonal nonmaximality, b <= a, no-FI-MAD consequences, arbitrary labels.
- `SeparationCardinal.lean`: existence of a minimum nonseparable AD cardinal.
- `Metatheory.lean`: genuine `Derives` and `Derives.Consistent` from YesMetaZFC.
- `Main.lean`: public entry point and paper-facing conditional cutoff.

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

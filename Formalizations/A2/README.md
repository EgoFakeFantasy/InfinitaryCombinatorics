# A2: monochromatic sets in strictly Delta-regressive colourings

This directory formalizes the mathematical results of Haoxuan Ye,
*Monochromatic sets in strictly Delta-regressive colourings* (A2), using the
repository's first-difference and pair-colouring library.
The preprint is archived on [Zenodo](https://doi.org/10.5281/zenodo.22846175).
The entry point is:

```lean
import Formalizations.A2.Paper
open InfinitaryCombinatorics.Formalizations.A2
```

## Proved results

- **Theorem 2.2:** for every ordinal `κ > ω`, every Delta-regressive colouring on
  `2^κ` has a monochromatic four-element set inside the zero cone, in a colour
  below `ω`. The ordinal and its universe are arbitrary; no regularity hypothesis
  or finite approximation replaces this statement.
- **Theorem 2.3:** the explicit colouring on `2^(ω+1)` has no five-clique and has a
  four-clique of colour zero.
- **Theorem 2.4:** every such colouring on `2^ω` into `ω` has a triangle.
- Lemma 3.1 and Corollary 3.2; the normalized embedding of Remark 3.3, including
  resetting the unconstrained first-difference-zero case to colour zero.
- The finite-terminal-colour variation in Remark 4.1, and the canonical-copy
  statement of Proposition 4.2 (no claim of a global no-five bound on longer spaces).
- The complete diagonal proof of the Lambie-Hanson--Soukup maximality lemma
  (Lemma 5.1), rigidity on the zero cone (Lemma 5.2), the explicit three-point
  calculation for Observation 2.1 of arXiv v2, and Proposition 5.3 with the
  colour set enlarged to `ω+1`.

See [the paper-to-code map](PAPER_COVERAGE.md) for precise declarations and
[the input audit](SOURCE_REVIEW.md) for what was retained and replaced.

## Representation

`Branch κ` is `Set.Iio κ → Bool`. `PairColoring` is a symmetric function whose
values on the diagonal are irrelevant. `HasClique n` explicitly includes an
embedding of `Fin n`, so all vertices are distinct. Regressivity is required
only for distinct points with positive first difference. No constraint at first
difference zero is silently added.

The triangle proof uses `ℕ → Bool` internally. `omegaEquiv` and the
first-difference transport lemmas identify it with the ordinal-indexed space;
`theorem_2_4` is exported with the paper's original domain and colour set.
All ordinal statements are universe-polymorphic. The `Theorem22`, `Theorem23`,
`Theorem24`, and `Proposition53` proposition definitions are acceptance
interfaces; each now has an unconditional theorem witness.

## Verification

Run `./verify.ps1` from the repository root, with the pinned Lean 4.30.0 and
mathlib revision. This checks the entire library, expanded acceptance statements,
module coverage, forbidden constructs, the unchanged R0 snapshot, source hashes,
and every project's transitive kernel dependencies. Permitted logical axioms are
only `propext`, `Classical.choice`, and `Quot.sound`.

Current evidence is in [the source manifest](../../verification/manifest.json),
[expanded statements](../../verification/formalizations-statements.log), and
[the axiom audit](../../verification/axiom-audit.log). CI repeats the same gate.
A build alone is not the criterion for accepting the paper's statements.

## Scope and attribution

This is a formalization of the stated paper results, not a claim of mathematical
priority or independent peer review. The maximality lemma and original problem
are due to Lambie-Hanson and Soukup; this development proves the used special
case internally. The correction is restricted to the displayed formula in
arXiv:2002.02480v2. The earlier cycle theorem, literature discussion, and questions
about infinite or uncountable monochromatic sets are not new proved claims here.

The original WorkBuddy contribution supplied valid sharpness proofs and useful
binary lemmas. The completion supplies the two missing main proofs, their full
supporting lemmas, boundary examples, transfer results, and integrated acceptance
checks. [Input hashes](input-source-hashes.json) identify the reviewed input.

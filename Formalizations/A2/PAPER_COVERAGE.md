# Paper coverage and semantic checks

The numbering is that of the A2 manuscript dated 20 September 2026; the
formalization update preserves it.

| Paper result | Declaration / file | Scope retained |
| --- | --- | --- |
| Definition 2.1 | `DeltaRegressive`, base `Delta.lean` | Positive first differences only; distinct vertices |
| Theorem 2.2 | `theorem_2_2`, `Four.lean` | All ordinals above omega; finite colour; four distinct points in the zero cone |
| Theorem 2.3 | `theorem_2_3`, `Theorem23.lean` | Explicit `sharpColoring`; no K5 and an explicit zero-colour K4 |
| Theorem 2.4 | `theorem_2_4`, `Triangle.lean` | Ordinal omega domain and ordinal omega colours, arbitrary universe |
| Lemma 3.1 | `lemma_3_1`, `Basic.lean`; `clique4_in`, `Cliques.lean` | Prescribed colour, disjoint sides, distinct vertices, membership |
| Corollary 3.2 | `corollary_3_2`, `Paper.lean` | Proved under the stronger generality `omega < κ`; no main-theorem premise |
| Remark 3.3 | `Normalization.lean` | Injective zero extension and preservation of first difference; regressive pullback into omega+1; zero reset and unchanged zero-cone edges |
| Remark 4.1 | `sharpness_finite_terminal_variation`, `SharpnessVariants.lean` | Arbitrary finite terminal colours may depend on the pair |
| Proposition 4.2 | `canonicalColoring_regressive`, `canonicalColoring_no_five_on_copy`, `canonical_range`, `Transfer.lean` | Regressivity on the full longer space; no K5 only on the specified canonical copy; includes endpoint equality |
| Lemma 5.1 | `delta_maximal`, `Fusion.lean` | Every map on the full Cantor space; the diagonal existence conclusion is proved internally |
| Lemma 5.2 | `rigid_on_zero_cone`, `Triangle.lean` | Natural-coordinate presentation, related to ordinal branches by `omegaEquiv`; no-triangle premise remains explicit |
| Three-point calculation in Section 5.1 | `observation_counterexample`, `Boundary.lean` | The actual three sequences are distinct; all three displayed colours equal 1 |
| Proposition 5.3 | `proposition_5_3`, `Boundary.lean` | Omega-length domain; omega+1 colour set; positive-delta regressivity and no triangle |

`Statements.lean` fixes the public acceptance types. `Check.lean` gives theorem
witnesses for all four existential/universal interfaces; root
`CheckFormalizations.lean` additionally expands the definitions, including
injectivity, vertex domain, colour codomain, and scope of the canonical copy.

The fusion recursion is on finite prefixes but its conclusion is a branch of
the full function space. Thus neither main proof uses a finite sample in place
of the infinite domain. The omega-coordinate endpoints in Theorem 2.2 are
constructed separately and their first difference is proved to equal omega.

The literature comparison in Remark 3.4 is explanatory context. The cited
cycle theorem is not assumed by any of the formal proofs. No theorem here
settles the remaining infinite/uncountable alternatives of the original problem.

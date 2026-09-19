# Paper coverage and semantic review

Specification: Haoxuan Ye, *Traces and replacements in non-fin-intersecting almost disjoint families*, 19 September 2026. The table concerns mathematical statements and their proofs, not historical attribution or the unresolved Question 4.10. New names below are in `InfinitaryCombinatorics.Formalizations.R0` unless specified otherwise.

| Paper statement | Checked declaration(s) | Source |
| --- | --- | --- |
| Lemma 2.2: transport and inheritance | shared `almostDisjoint_equiv`, `finIntersecting_equiv`, `not_finIntersecting_of_subset`; `mad_image`; `Cardinal.mk_image_eq` | shared library; UniformMAD |
| Proposition 2.3: lower bound | `small_families_are_finIntersecting` | Main |
| Theorem 3.1: attained minimum s | `exists_counterexample_of_size_s`, `least_counterexample_cardinal`, `nonFinIntersectingNumber_eq_splittingNumber` | Main; original R0 snapshot |
| Remark 3.2: explicit interval coding | `binaryWordCode_interval`, `binaryWordCode_injective`, `binaryWordCode_surjective`, `binaryWordEquivNat` | BinaryCoding |
| Lemma 3.3: exact realization | `exact_trace_realization` | TraceRealization; Selectors |
| Corollary 3.4: full spectrum | `nonFinIntersecting_cardinal_spectrum` | Spectrum |
| Theorem 4.1: replacement | `refinement_ad`, `refinement_orthogonal`, `refinement_maximal`, `refinement_mad` | Local |
| Corollary 4.2: finite replacement | `finite_cover_maximalOn`, `finite_refinement_card` | Local |
| Equation (4.1), Definition 4.3, (4.2) | `remainder_iff_completion`, `exists_minimum_remainder`, `remainder_orthogonal_invariance`, `extensionCost_orthogonal_invariance` | Remainder |
| Split seed / full branches comparison | `treeFamily_orthogonal`, `treeFamily_extensionCost` | BranchComparison |
| Theorem 5.1: uniform MAD of size c | `uniform_nonFinIntersecting_mad_tree`, `uniform_nonFinIntersecting_mad` | UniformMAD |
| Lemma 6.1: countable completion | `countable_completion`, `countable_infinite_mad_extension` | CountableCompletion |
| Theorem 6.2: both cost inequalities | `local_to_global_extension_bounds` | LocalGlobal |
| Corollary 6.3: transfer and non-FI | `countable_incidence_transfer`, `nonFinIntersecting_countable_incidence_transfer` | CountableTransfer |
| Proposition 6.4: placement formula | `placement_formula`, `placement_at_a_iff` | Placement |
| Theorem 7.1: fixed trace assignment | `trace_splitting_replacement` | BinarySplitting |
| Proposition 7.2: hitting / obstruction | `mad_trace_hitting`, `no_trace_splitting_of_pairwise_finite` | BinarySplitting |
| Singleton-block consequence | `singleton_trace`, `singleton_blocks_obstruction` | Consequences |
| Appendix A: explicit triangle | `triangleValue_le`, `triangleValue_ne_of_bit`, `triangleHalf_trace`, `triangleHalf_inter_same`, `triangleHalf_inter_ne`, `triangleFamily_card`, `triangle_counterexample` | Triangle; Consequences |

## Representation and proof-method differences

1. The old `R0.Node = Nat × Finset Nat` is a countable ambient type containing unused pairs; its blocks are exactly the valid words at each level. Bijection transport preserves the original Nat theorem. The new `BinaryWord` and `binaryWordEquivNat` separately verify the exact big-endian interval enumeration in Remark 3.2. The precise triangular subtype in Appendix A has no extraneous points.
2. Theorem 5.1 uses `exists_mad_extension`, proved by Zorn's lemma, to complete all branches. The paper presents the equivalent well-ordered greedy completion. Both use classical choice; the Lean result does not assert a choice-free or parameter-free definable completion. Subsequent splitting and the exact continuum cardinality are proved, not assumed.
3. The spectrum proof enlarges a minimum regular splitting family inside the continuum-sized space of infinite coinfinite sets, then applies the same tree construction. This proves the same exact spectrum as the paper's unused-branch padding argument.
4. Lemma 3.3 uses the dependent index `(h : H) × U h`. Its injective output distinguishes every indexed set, including two supports assigned to one branch. It proves exact traces, support in the union of blocks, and at most one point per block. Block growth is `∀ k, ∃ N, ∀ n ≥ N, k ≤ blockSize C n`.
5. `ADFamily` permits finite and empty families; every member is infinite. `R0.AlmostDisjoint` adds infinitude of the family, and `MAD` uses that infinite convention. `MaximalOn` deliberately allows finite local completions. Countable completion returns the exact original members, not just sets equal modulo finite errors.
6. `Orthogonal` includes finite sets. `Remainder` is supported on its specified ground set; it is AD, orthogonal to the old family and maximal among infinite orthogonal sets. `extensionCost` is its attained minimum cardinality, including zero and finite values. On AD families this is proved equivalent to the paper's completion definition.
7. `almostDisjointnessNumber` is the attained least size of an infinite MAD family on Nat. Transport proves its usual meaning on every countably infinite ground set; it is not an external constant or axiom. The transfer and placement theorems retain countability of the ground set and infinitude of the seed.
8. The trace condition fixes `S : Set X → Set Nat` before all infinite `I`. Extending an assignment on a subfamily to this total function is harmless because only members of that subfamily are used. Finite pieces are removed by `binaryParts`; blocks need not cover the ground set. The obstruction requires pairwise finite traces for distinct indexed members, even if two trace values coincide.
9. Question 4.10 and any new inequality involving the invariant ie are not theorems of this development. No existence of the missing trace assignment or small extension remainder is postulated.

## Verification evidence

`CheckFormalizations.lean` restates key results with maximality, incidence and trace predicates expanded. `Audit.lean` requires the named milestones and traverses all project declarations, including generated and private declarations, checking transitive axiom dependencies. `verify.ps1` also rejects unimported modules and source changes during checking. The original R0 byte hashes are unchanged.

The manifest records exact toolchain, dependency revision, source hashes, check time and declaration counts. A successful GitHub workflow run is separate evidence for its own commit; the generated paper links the fixed source revision and that run. Mathematical formalization does not establish publication priority or independent human refereeing.

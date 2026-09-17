import Formalizations
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let required : Array Name := #[
    `InfinitaryCombinatorics.mad_iff_maximal,
    `InfinitaryCombinatorics.exists_unsplit_of_countable,
    `InfinitaryCombinatorics.aleph0_lt_splittingNumber,
    `InfinitaryCombinatorics.finIntersecting_of_countable,
    `InfinitaryCombinatorics.ideal_proper_of_infinite_ad,
    `InfinitaryCombinatorics.PairColoring.blocksExtensions_iff,
    `InfinitaryCombinatorics.delta_spec,
    `InfinitaryCombinatorics.exists_boundedDepth_unboundedWidth,
    `InfinitaryCombinatorics.Directed.isDicoloring_iff_fibers,
    `InfinitaryCombinatorics.pr1Witness_recolor,
    `R0.nonFinIntersectingNumber_eq_splittingNumber,
    `InfinitaryCombinatorics.Formalizations.R0.small_families_are_finIntersecting,
    `InfinitaryCombinatorics.Formalizations.R0.exists_counterexample_of_size_s,
    `InfinitaryCombinatorics.Formalizations.R0.least_counterexample_cardinal,
    `InfinitaryCombinatorics.Formalizations.R0.nonFinIntersectingNumber_eq_splittingNumber,
    `InfinitaryCombinatorics.Formalizations.A1.cantorPair_unpair,
    `InfinitaryCombinatorics.Formalizations.A1.cantorFst_pair,
    `InfinitaryCombinatorics.Formalizations.A1.cantorSnd_pair,
    `InfinitaryCombinatorics.Formalizations.A1.le_cantorPair_left,
    `InfinitaryCombinatorics.Formalizations.A1.typeSeq_depth,
    `InfinitaryCombinatorics.Formalizations.A1.typeSeq_order,
    `InfinitaryCombinatorics.Formalizations.A1.typeSeqW_boundedDepth,
    `InfinitaryCombinatorics.Formalizations.A1.cantorPair_closedForm,
    `InfinitaryCombinatorics.Formalizations.A1.countable_initialSegment,
    `InfinitaryCombinatorics.Formalizations.A1.countable_convex_partition,
    `InfinitaryCombinatorics.Formalizations.A1.two_gaps,
    `InfinitaryCombinatorics.Formalizations.A1.typeGuessing_iff_allPoints,
    `InfinitaryCombinatorics.Formalizations.A1.typeGuessing_implies_hits_thin,
    `InfinitaryCombinatorics.Formalizations.A1.typeGuessing_implies_K_thin,
    `InfinitaryCombinatorics.Formalizations.A1.G_implies_KA,
    `InfinitaryCombinatorics.Formalizations.A1.BDTG_implies_KA,
    `InfinitaryCombinatorics.Formalizations.A1.not_G_of_not_KA,
    `InfinitaryCombinatorics.Formalizations.A1.antiColoring_on_omegaOne,
    `InfinitaryCombinatorics.Formalizations.A1.Diamond_implies_ClubGuessing,
    `InfinitaryCombinatorics.Formalizations.A1.KA_implies_KAomegaOne]
  for name in required do
    unless env.contains name do
      throwError "Required declaration missing: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations := 0
  let mut theorems := 0
  let mut used : Array Name := #[]
  for (name, info) in env.constants.toList do
    -- Also include private declarations and generated structure eliminators.
    let components := name.toString.splitOn "."
    if components.contains "InfinitaryCombinatorics" || components.contains "R0" then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
        unless used.contains ax do
          used := used.push ax
      if info.isTheorem then
        logInfo m!"{name}: {axioms}"
  unless theorems > 0 do
    throwError "No project theorem declarations were audited"
  logInfo m!"Kernel audit passed: {declarations} declarations, {theorems} theorem constants; axioms: {used}"

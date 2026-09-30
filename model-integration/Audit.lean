import FIMADModels
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let required : Array Name := #[
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.omega_all,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.omega_sup,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.unbounded_eq_tails,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.unbounded_witnesses,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.hits_force_unbounded,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.split_unbounded_names,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.algebra,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.natural_decisions_dense,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.natural_eq_of_ne,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.small_value_eq_bot,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.decisions_disjoint,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.real_mem,
    `InfinitaryCombinatorics.Formalizations.FIMAD.PosetRegular.real_subset_omega,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient.truth,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient.models_zfc,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient.extensional,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.BooleanQuotient.model_of_nonzero,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.positive_model_of_nonzero,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.negative_model_of_not_top,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.consistency_of_nonzero,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.native_semantics,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.value_correct,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.positive_consistency,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.negative_consistency,
    `InfinitaryCombinatorics.Formalizations.FIMAD.TypedModels.CheckedBooleanZFC.models_zfc]
  for name in required do
    unless env.contains name do
      throwError "Required declaration missing: {name}"
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (name.toString.splitOn ".").contains "InfinitaryCombinatorics" || required.contains name then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      let axioms ← collectAxioms name
      for ax in axioms do
        unless permitted.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      if info.isTheorem then
        logInfo m!"{name}: {axioms}"
  logInfo m!"Typed model audit passed: {declarations} declarations, {theorems} theorem constants"

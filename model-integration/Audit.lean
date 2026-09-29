import FIMADModels
import Lean

open Lean Elab Command in
run_elab do
  let env ← getEnv
  let required : Array Name := #[
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

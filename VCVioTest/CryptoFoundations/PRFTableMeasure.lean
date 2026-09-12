/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import Examples.PRFTagReader.MultipleToHybrid.EagerSetup
public import VCVio.EvalDist.PFunctorMeasure.Core

/-!
# Measure-based cache and observation checks

The core dependency check follows theorem proofs and types. The cache-list example
uses native free-program semantics with explicit sampling laws and repeated keys.
-/

public section

open OracleSpec OracleComp MeasureTheory ProbabilityTheory

run_cmd do
  let env ← Lean.getEnv
  let mut pending := [``OracleComp.evalDist_bind_congr_of_support,
    ``evalDist_bind_bind_update, ``evalDist_bind_cell_extract,
    ``evalDist_bind_bind_bind_update_two_map, ``evalDist_map_table_comp_injective]
  let mut visited : Std.HashSet Lean.Name := {}
  while let name :: rest := pending do
    pending := rest
    unless visited.contains name do
      visited := visited.insert name
      for forbidden in [`PMF, `SPMF, `evalSPMF, `probEvent, `probOutput, `expectedValue] do
        if forbidden.isPrefixOf name then
          throwError "native table proof depends on the discrete declaration {name}"
      if let some info := env.find? name then
        pending := info.getUsedConstantsAsSet.toList ++ pending

namespace VCVioTest.PRFTableMeasure

variable [unifSpec.toPFunctor.IsMeasureSpec]

example (hvalue : 𝒟[$ᵗ Bool] = uniformOn Set.univ)
    (htable : 𝒟[$ᵗ (Fin 3 → Bool)] = uniformOn Set.univ)
    (cont : (Fin 3 → Bool) → ProbComp ℝ) :
    𝒟[do let r ← PRFTagReader.idealCacheMapM [0, 2, 0, 2] ∅
          let g ← $ᵗ (Fin 3 → Bool)
          cont (tableExtending r.2 g)] =
      𝒟[do let g ← $ᵗ (Fin 3 → Bool); cont g] := by
  simpa only [tableExtending_empty] using
    PRFTagReader.evalDist_idealCacheMapM_bind_uniformTable_comp hvalue htable [0, 2, 0, 2] ∅ cont

end VCVioTest.PRFTableMeasure

/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
import all VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.Chain.Simulation

/-!
# Structural fork-handler invariant checks

The cache/log transition proofs have no probability dependencies. Concrete fresh,
repeated, and signing updates exercise the two invariants on the same transition relation.
-/

public section

open OracleSpec OracleComp FiatShamir.Stateful

run_cmd do
  let env ← Lean.getEnv
  let mut pending := [``FiatShamir.Stateful.ForkStateStep.preserves_aware,
    ``FiatShamir.Stateful.ForkStateStep.preserves_live_adv]
  let mut visited : Std.HashSet Lean.Name := {}
  while let name :: rest := pending do
    pending := rest
    unless visited.contains name do
      visited := visited.insert name
      for forbidden in [`PMF, `SPMF, `evalSPMF, `probEvent, `probOutput, `IsUniformSpec,
          `IsProbabilitySpec, `SampleableType] do
        if forbidden.isPrefixOf name then
          throwError "structural invariant proof depends on probability declaration {name}"
      if let some info := env.find? name then
        pending := info.getUsedConstantsAsSet.toList ++ pending

namespace VCVioTest.FiatShamirStateSteps

example (s : ForkBaseState ℕ ℕ Bool × List ℕ)
    (hs : forkAwareInv (M := ℕ) s) (hadv : forkLiveCacheAdvCacheInv (M := ℕ) s)
    (mc : ℕ × ℕ) :
    let s' := ((s.1.1.cacheQuery (.inr mc) true,
      s.1.2.1.cacheQuery mc true, s.1.2.2 ++ [mc]), s.2)
    forkAwareInv (M := ℕ) s' ∧ forkLiveCacheAdvCacheInv (M := ℕ) s' := by
  exact ⟨ForkStateStep.preserves_aware (M := ℕ) (.fresh mc true) hs,
    ForkStateStep.preserves_live_adv (M := ℕ) (.fresh mc true) hadv⟩

example (s : ForkBaseState ℕ ℕ Bool × List ℕ)
    (hs : forkAwareInv (M := ℕ) s) (hadv : forkLiveCacheAdvCacheInv (M := ℕ) s)
    (mc : ℕ × ℕ) (hmiss : s.1.1 (.inr mc) = none) :
    let s' := ((s.1.1.cacheQuery (.inr mc) false, s.1.2), s.2 ++ [mc.1])
    forkAwareInv (M := ℕ) s' ∧ forkLiveCacheAdvCacheInv (M := ℕ) s' := by
  exact ⟨ForkStateStep.preserves_aware (M := ℕ) (.signedFresh mc false hmiss) hs,
    ForkStateStep.preserves_live_adv (M := ℕ) (.signedFresh mc false hmiss) hadv⟩

example (s : ForkBaseState ℕ ℕ Bool × List ℕ)
    (hs : forkAwareInv (M := ℕ) s) (hadv : forkLiveCacheAdvCacheInv (M := ℕ) s)
    (mc : ℕ × ℕ) (hhit : s.1.2.1 mc = some true) :
    let s' := ((s.1.1.cacheQuery (.inr mc) true, s.1.2), s.2)
    forkAwareInv (M := ℕ) s' ∧ forkLiveCacheAdvCacheInv (M := ℕ) s' := by
  exact ⟨ForkStateStep.preserves_aware (M := ℕ) (.cached mc true hhit) hs,
    ForkStateStep.preserves_live_adv (M := ℕ) (.cached mc true hhit) hadv⟩

end VCVioTest.FiatShamirStateSteps

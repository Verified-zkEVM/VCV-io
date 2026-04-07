/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.Fork

/-!
# Value-Carrying Fork Wrappers

This file extends `VCVio.CryptoFoundations.Fork` with fork wrappers that expose the old and new
oracle values at the chosen fork point.

The basic `fork` API only returns the two outputs of the forked executions. For
special-soundness extractors we also need the corresponding challenge values. The definitions
here keep the same replay pattern as `fork`, but package the return value as:

- the first output;
- the original seeded value at the chosen fork point;
- the second output;
- the fresh replacement value.

If the chosen fork point lies past the seeded prefix, the wrapper returns `none`, since there is
no original value to pair with the replacement value.
-/

open OracleSpec OracleComp

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} {α : Type}

section forkValues

variable [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]

/-- Deterministic postprocessing of [`forkWithSeedValue`] that re-attaches the original query
value at the chosen fork point, when that point lies within the sampled seed. -/
def attachForkQueryValues
    (qb : ι → ℕ) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    (seed : QuerySeed spec) (u : spec.Range i) :
    Option (α × α) → Option (α × spec.Range i × α × spec.Range i)
  | none => none
  | some (x₁, x₂) =>
      match cf x₁ with
      | none => none
      | some s =>
          match (seed i)[↑s]? with
          | none => none
          | some u₀ => some (x₁, u₀, x₂, u)

/-- Forking wrapper that exposes the original and replacement values at the chosen fork point.

Operationally this is the same fork core as [`fork`], with the same seed generation and replay
pattern. The only difference is the return payload: on success it includes both the original
seeded value and the fresh replacement value at the chosen oracle family `i`. -/
def forkWithQueryValues (main : OracleComp spec α)
    (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × spec.Range i × α × spec.Range i)) := do
  let seed ← liftComp (generateSeed spec qb js) spec
  let u ← liftComp ($ᵗ spec.Range i) spec
  let r ← forkWithSeedValue main qb i cf seed u
  return attachForkQueryValues (qb := qb) (i := i) (cf := cf) seed u r

end forkValues

end OracleComp

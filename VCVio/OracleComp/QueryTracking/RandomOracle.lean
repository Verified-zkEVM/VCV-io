/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.Constructions.GenerateSeed

/-!
# Random Oracle Implementations

This file defines two oracle implementations built from uniform sampling:

* **`randomOracle`** (lazy, consistent): Samples a fresh uniform value on first query and caches
  for future consistency. Same input always yields same output. State: `QueryCache`.
  This is `uniformSampleImpl.withCaching`.

* **`eagerRandomOracle`** (pre-seeded, independent): Serves answers from a pre-generated
  `QuerySeed`, consuming values sequentially. Falls back to fresh uniform sampling when
  exhausted. Different calls to the same oracle consume different seed values.
  State: `QuerySeed`.

These two models differ when an oracle is queried more than once: the lazy version returns
the cached value (consistency), while the eager version consumes the next seed value
(independence). When averaged over a uniformly sampled seed, the eager version matches
the fresh independent-query semantics of `evalDist`; it does *not* coincide with the
lazy cached `randomOracle` on repeated queries.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι}

/-- The (lazy) random oracle: uniform sampling with caching.
On query `t`, returns the cached value if present, otherwise samples `$ᵗ spec.Range t`
uniformly and caches the result. This ensures consistency: same input → same output. -/
@[inline, reducible] def randomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT spec.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

namespace randomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0,0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    (randomOracle (spec := spec₀)) t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← $ᵗ spec₀.Range t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

end randomOracle

/-- The eager random oracle: serves answers from a pre-generated `QuerySeed`, consuming
seed values sequentially and falling back to fresh uniform sampling when exhausted.

Concretely, on query `t`:
- If `seed t` is non-empty, return the head and advance to the tail.
- If `seed t` is empty, sample `$ᵗ spec.Range t` uniformly and leave the seed unchanged.

**Important**: This gives INDEPENDENT samples (each call consumes a different seed value),
unlike `randomOracle` which gives CONSISTENT samples (same input → same output via caching).
The two models agree when no oracle index is queried more than once.

This is definitionally equal to `uniformSampleImpl.withPregen` (from `SeededOracle.lean`). -/
@[inline, reducible] def eagerRandomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT (QuerySeed spec) ProbComp) :=
  fun t => StateT.mk fun seed =>
    match seed t with
    | u :: us => pure (u, Function.update seed t us)
    | [] => (·, seed) <$> ($ᵗ spec.Range t)

namespace eagerRandomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0,0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    (eagerRandomOracle (spec := spec₀)) t = StateT.mk fun seed =>
      match seed t with
      | u :: us => pure (u, Function.update seed t us)
      | [] => (·, seed) <$> ($ᵗ spec₀.Range t) := rfl

/-- With an empty seed, the eager random oracle reduces to `uniformSampleImpl`:
every query falls through to fresh uniform sampling with no state change.
This is a faithful simulation (preserves `evalDist`). -/
theorem evalDist_simulateQ_run'_empty [spec₀.Fintype] [spec₀.Inhabited]
    {α : Type} (oa : OracleComp spec₀ α) :
    evalDist ((simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' ∅) = evalDist oa := by
  sorry

end eagerRandomOracle

/-- The eager random oracle, averaged over a uniformly sampled seed, matches the
fresh independent-query semantics of `evalDist`. This is because the pre-sampled
seed values are i.i.d. uniform, exactly matching fresh oracle queries.

This is the analog of `seededOracle.evalDist_liftComp_generateSeed_bind_simulateQ_run'`
but for `eagerRandomOracle` (which falls back to `ProbComp` rather than `OracleComp spec`). -/
theorem eagerRandomOracle_evalDist_generateSeed_bind {ι₀ : Type} [DecidableEq ι₀]
    {spec₀ : OracleSpec.{0,0} ι₀}
    [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]
    [spec₀.Fintype] [spec₀.Inhabited]
    {α : Type} (oa : OracleComp spec₀ α)
    (qc : ι₀ → ℕ) (js : List ι₀) :
    evalDist (do
      let seed ← generateSeed spec₀ qc js
      (simulateQ (eagerRandomOracle (spec := spec₀)) oa).run' seed) = evalDist oa := by
  sorry

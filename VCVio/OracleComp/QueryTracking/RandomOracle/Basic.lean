/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Lazy Random Oracle

The (lazy) random oracle samples a fresh uniform value on first query and caches the result
for future consistency. Same input always yields same output. State: `QueryCache`.
This is `uniformSampleImpl.withCaching`.
-/

open OracleComp OracleSpec

/-- The (lazy) random oracle: uniform sampling with caching.
On query `t`, returns the cached value if present, otherwise samples `$ᵗ spec.Range t`
uniformly and caches the result. This ensures consistency: same input → same output. -/
@[inline, reducible] def OracleSpec.randomOracle {ι} [DecidableEq ι] {spec : OracleSpec ι}
    [∀ t : spec.Domain, SampleableType (spec.Range t)] :
    QueryImpl spec (StateT spec.QueryCache ProbComp) :=
  uniformSampleImpl.withCaching

namespace randomOracle

variable {ι₀ : Type} [DecidableEq ι₀] {spec₀ : OracleSpec.{0, 0} ι₀}
  [∀ t : spec₀.Domain, SampleableType (spec₀.Range t)]

lemma apply_eq (t : spec₀.Domain) :
    spec₀.randomOracle t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← $ᵗ spec₀.Range t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

end randomOracle

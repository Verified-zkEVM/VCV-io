/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.SimSemantics.Constructions

/-!
# Caching Queries Made by a Computation

This file defines a modifier `QueryImpl.withCaching` that modifies a query implementation to
cache results to return to the same query in the future.

We also define a plain caching oracle and random oracles as special cases of this.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} [DecidableEq ι] {spec : OracleSpec} [spec.DecidableEq]

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a query implementation to cache previous call and return that output in the future. -/
def withCaching (so : QueryImpl spec m) : QueryImpl spec (StateT spec.QueryCache m) :=
  fun t => do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)

@[simp] lemma withCaching_apply (so : QueryImpl spec m) (t : spec.domain) :
    so.withCaching t = (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← so t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

end QueryImpl

/-- Oracle for caching queries to the oracles in `spec`, querying fresh values if needed. -/
@[inline, reducible] def cachingOracle :
    QueryImpl spec (StateT spec.QueryCache (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withCaching

namespace cachingOracle

lemma apply_eq (t : spec.domain) : cachingOracle t =
  (do match (← get) t with
    | Option.some u => return u
    | Option.none =>
        let u ← query t
        modifyGet fun cache => (u, cache.cacheQuery t u)) := rfl

end cachingOracle

-- -- NOTE: need to change universe levels b/c `unifSpec` doesn't use `pNat`.
-- variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

-- /-- Random Oracle implemented as a uniform selection oracle with caching -/
-- @[inline, reducible] def randomOracle [(i : spec.domain) → SampleableType (spec.range i)] :
--     QueryImpl spec (StateT spec.QueryCache (OracleComp unifSpec)) :=
--   unifOracle.withCaching

-- namespace randOracle

-- variable [(i : ι) → SampleableType (spec.range i)]

-- lemma apply_eq {α} (q : OracleQuery spec α) : randomOracle.impl q =
--     match q with | query i t => (do match (← get) i t with
--       | Option.some u => return u
--       | Option.none =>
--           let u ←$ᵗ (spec.range i)
--           modifyGet fun cache => (u, cache.cacheQuery i t u)) := rfl

-- end randOracle

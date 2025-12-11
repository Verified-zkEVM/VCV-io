/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.Constructions.GenerateSeed
import VCVio.OracleComp.Coercions.SubSpec


/-!
# Pre-computing Results of Oracle Queries

This file defines a function `QueryImpl.withPregen` that modifies a query implementation
to take in a list of pre-chosen outputs to use when answering queries.

Note that ordering is subtle, for example `so.withCaching.withPregen` will first check for seeds
and not cache the result if one is found, while `so.withPregen.withCaching` checks the cache first,
and include seed values into the cache after returning them.
-/

open OracleComp OracleSpec

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} [DecidableEq ι]

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Modify a `QueryImpl` to check for pregenerated responses for oracle queries first -/
def withPregen (so : QueryImpl spec m) : QueryImpl spec (ReaderT spec.QuerySeed m) where
  impl | query i t => do
    let seed ← read
    do match seed i with
      | u :: us => ReaderT.adapt (fun seed => seed.update i us) (return u)
      | [] => so.impl (query i t)

@[simp] lemma withPregen_apply {α} (so : QueryImpl spec m) (q : OracleQuery spec α) :
    so.withPregen.impl q = match q with | query i t => (do
    let seed ← read
    do match seed i with
      | u :: us => ReaderT.adapt (fun seed => seed.update i us) (return u)
      | [] => so.impl (query i t)) := rfl

end QueryImpl

/-- Use pregenerated oracle responses for queries. -/
@[inline, reducible] def seededOracle [DecidableEq ι] :
    QueryImpl spec (ReaderT (QuerySeed spec) (OracleComp spec)) :=
  idOracle.withPregen

namespace seededOracle

lemma apply_eq {α} (q : OracleQuery spec α) :
    seededOracle.impl q = match q with | query i t => (do
      let seed ← read
      do match seed i with
        | u :: us => ReaderT.adapt (fun seed => seed.update i us) (return u)
        | [] => query i t) := rfl

@[simp]
lemma probOutput_generateSeed_bind_simulateQ_bind {ι : Type _} {spec : OracleSpec ι}
    {α β : Type _} [DecidableEq ι]
    [∀ i, SelectableType (spec.range i)] [unifSpec ⊂ₒ spec] [spec.FiniteRange]
    (qc : ι → ℕ) (js : List ι)
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    [= y | do
      let seed ← liftComp (generateSeed spec qc js) spec
      let x ← (simulateQ seededOracle oa).run seed
      ob x] = [= y | oa >>= ob] := by
  sorry

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ {ι : Type _} {spec : OracleSpec ι}
    {α β : Type _} [DecidableEq ι]
    [∀ i, SelectableType (spec.range i)] [unifSpec ⊂ₒ spec] [spec.FiniteRange]
    (qc : ι → ℕ) (js : List ι)
    (oa : OracleComp spec α) (f : α → β) (y : β) :
    [= y | do
      let seed ← liftComp (generateSeed spec qc js) spec
      f <$> (simulateQ seededOracle oa).run seed] = [= y | f <$> oa] := by
  sorry

end seededOracle

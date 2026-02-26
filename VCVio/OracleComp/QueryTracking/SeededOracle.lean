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

/-- Modify a `QueryImpl` to check for pregenerated responses for oracle queries first.
If a seed value is available for the query, it is used instead of calling the oracle. -/
def withPregen (so : QueryImpl spec m) :
    QueryImpl spec (ReaderT (QuerySeed spec) m) :=
  fun t => do
    let seed ← read
    match seed t with
    | u :: us => ReaderT.adapt (fun seed => Function.update seed t us) (return u)
    | [] => so t

@[simp, grind =]
lemma withPregen_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withPregen t = (do
      let seed ← read
      match seed t with
      | u :: us => ReaderT.adapt (fun seed => Function.update seed t us) (return u)
      | [] => so t) := rfl

end QueryImpl

/-- Use pregenerated oracle responses for queries, falling back to the real oracle
when the seed is exhausted. -/
def seededOracle :
    QueryImpl spec (ReaderT (QuerySeed spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withPregen

namespace seededOracle

@[simp]
lemma apply_eq (t : spec.Domain) :
    seededOracle t = (do
      let seed ← read
      match seed t with
      | u :: us => ReaderT.adapt (fun seed => Function.update seed t us) (return u)
      | [] => query t) := rfl

@[simp]
lemma probOutput_generateSeed_bind_simulateQ_bind
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (ob : α → OracleComp spec₀ β) (y : β) :
    Pr[= y | do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      let x ← (simulateQ seededOracle oa).run seed
      ob x] = Pr[= y | oa >>= ob] := by
  sorry

@[simp]
lemma probOutput_generateSeed_bind_map_simulateQ
    {ι₀ : Type} {spec₀ : OracleSpec ι₀} [DecidableEq ι₀]
    [∀ i, SampleableType (spec₀.Range i)] [unifSpec ⊂ₒ spec₀]
    [spec₀.Fintype] [spec₀.Inhabited]
    (qc : ι₀ → ℕ) (js : List ι₀)
    {α β : Type} (oa : OracleComp spec₀ α) (f : α → β) (y : β) :
    Pr[= y | (do
      let seed ← liftComp (generateSeed spec₀ qc js) spec₀
      f <$> (simulateQ seededOracle oa).run seed : OracleComp spec₀ β)] =
      Pr[= y | f <$> oa] := by
  sorry

end seededOracle

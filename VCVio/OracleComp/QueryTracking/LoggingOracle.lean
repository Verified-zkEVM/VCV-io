/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.SimSemantics.WriterT
import VCVio.OracleComp.SimSemantics.Constructions
import VCVio.OracleComp.QueryTracking.Structures

/-!
# Logging Queries Made by a Computation

-/

universe u v w

open OracleSpec OracleComp

variable {ι : Type u} {spec : OracleSpec}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

def withLogging (so : QueryImpl spec m) : QueryImpl spec (WriterT (QueryLog spec) m) :=
  fun t => do
    let u ← so t
    tell (QueryLog.singleton t u)
    return u

-- /-- Add logging to an existing query implementation, using `StateT` to extend the final monad. -/
-- def withLogging (so : QueryImpl spec m) :
--     QueryImpl spec (WriterT (QueryLog spec) m) where
--   impl | q => do
--     let x ← liftM (so.impl q)
--     tell (QueryLog.singleton q x)
--     return x

-- @[simp] lemma withLogging_apply {α} (so : QueryImpl spec m) (q : OracleQuery spec α) :
--     so.withLogging.impl q =
--       do let x ← liftM (so.impl q); tell (QueryLog.singleton q x); return x := rfl

end QueryImpl

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle : QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec)) :=
  idOracle.withLogging

namespace loggingOracle

-- variable {ι : Type u} {spec : OracleSpec ι} {α β : Type u}

-- @[simp] lemma apply_eq (q : OracleQuery spec α) : loggingOracle.impl q =
--     do let u ← q; tell (QueryLog.singleton q u); return u := rfl

-- /-- Taking only the main output after logging queries is the original compuation. -/
-- @[simp]
-- lemma fst_map_run_simulateQ (oa : OracleComp spec α) :
--     (Prod.fst <$> (simulateQ loggingOracle oa).run) = oa :=
--   fst_map_writerT_run_simulateQ (by simp) oa

-- /-- Throwing away the query log after simulation looks like running the original computation. -/
-- @[simp]
-- lemma run_simulateQ_bind_fst (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
--     ((simulateQ loggingOracle oa).run >>= fun x => ob x.1) = oa >>= ob := by
--   rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]

-- @[simp]
-- lemma probFailure_run_simulateQ [spec.FiniteRange] (oa : OracleComp spec α) :
--     [⊥ | (simulateQ loggingOracle oa).run] = [⊥ | oa] :=
--   probFailure_writerT_run_simulateQ (by simp) (by simp) oa

-- @[simp]
-- lemma NeverFail_run_simulateQ_iff (oa : OracleComp spec α) :
--     NeverFail (simulateQ loggingOracle oa).run ↔ NeverFail oa :=
--   NeverFail_writerT_run_simulateQ_iff (by simp) (by sorry) oa

-- alias ⟨_, NeverFail_simulateQ⟩ := NeverFail_run_simulateQ_iff

end loggingOracle

/-- Add a query log to a computation using a logging oracle.  -/
@[reducible] def OracleComp.withQueryLog {α} (mx : OracleComp spec α) :
    OracleComp spec (α × QueryLog spec) :=
  WriterT.run (simulateQ idOracle.withLogging mx)

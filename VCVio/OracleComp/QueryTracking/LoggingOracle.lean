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

variable {ι} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-- Given that `so` implements the oracles in `spec` using the monad `m`,
`withLogging so` gives the same implementation in the extension `WriterT (QueryLog spec) m`,
by logging all the queries to the writer monad before forwarding the response. -/
def withLogging (so : QueryImpl spec m) : QueryImpl spec (WriterT (QueryLog spec) m) :=
  fun t : spec.Domain => do let u ← so t; tell [⟨t, u⟩]; return u

@[simp, grind =]
lemma withLogging_apply (so : QueryImpl spec m) (t : spec.Domain) :
    so.withLogging t = do let u ← so t; tell [⟨t, u⟩]; return u := rfl

lemma fst_map_run_withLogging [LawfulMonad m] (so : QueryImpl spec m) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withLogging) mx).run =
    simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

end QueryImpl

/-- Simulation oracle for tracking the quries in a `QueryLog`, without modifying the actual
behavior of the oracle. Requires decidable equality of the indexing set to determine
which list to update when queries come in. -/
def loggingOracle {spec : OracleSpec ι} :
    QueryImpl spec (WriterT (QueryLog spec) (OracleComp spec)) :=
  (QueryImpl.ofLift spec (OracleComp spec)).withLogging

namespace loggingOracle

@[simp] -- TODO: more general version/class for query impls that never have failures
lemma probFailure_simulateQ {spec : OracleSpec.{0,0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    Pr[⊥ | (WriterT.run
        (simulateQ (loggingOracle (spec := spec)) oa) :
          OracleComp spec (α × spec.QueryLog))] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

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
-- @[simp]
-- lemma neverFails_run_simulateQ_iff (oa : OracleComp spec α) :
--     neverFails (simulateQ loggingOracle oa).run ↔ neverFails oa :=
--   neverFails_writerT_run_simulateQ_iff (by simp) (by simp only [apply_eq, liftM_query_writerT,
--     bind_pure_comp, WriterT.run_bind, WriterT.run_monadLift, QueryLog.monoid_one_def,
--     QueryLog.monoid_mul_def, WriterT.run_map, WriterT.run_tell, map_pure, Prod.map_apply, id_eq,
--     Functor.map_map, List.nil_append, neverFails_map_iff, neverFails_query, implies_true]) oa

-- alias ⟨_, NeverFail_simulateQ⟩ := NeverFail_run_simulateQ_iff

end loggingOracle

/-- Add a query log to a computation using a logging oracle.  -/
@[reducible] def OracleComp.withQueryLog {α} (mx : OracleComp spec α) :
    OracleComp spec (α × QueryLog spec) :=
  WriterT.run (simulateQ (QueryImpl.ofLift spec (OracleComp spec)).withLogging mx)

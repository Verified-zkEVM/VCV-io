/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
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


@[simp]
lemma probFailure_simulateQ {spec : OracleSpec.{0,0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    Pr[⊥ | (WriterT.run
        (simulateQ (loggingOracle (spec := spec)) oa) :
          OracleComp spec (α × spec.QueryLog))] = Pr[⊥ | oa] := by
  simp only [HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma fst_map_run_simulateQ {spec : OracleSpec.{0,0} ι} {α : Type}
    (oa : OracleComp spec α) :
    Prod.fst <$> (simulateQ (loggingOracle (spec := spec)) oa).run = oa := by
  rw [loggingOracle, QueryImpl.fst_map_run_withLogging, simulateQ_ofLift_eq_self]

@[simp]
lemma run_simulateQ_bind_fst {spec : OracleSpec.{0,0} ι} {α β : Type}
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    ((simulateQ (loggingOracle (spec := spec)) oa).run >>= fun x => ob x.1) = oa >>= ob := by
  rw [← bind_map_left Prod.fst, fst_map_run_simulateQ]

@[simp]
lemma NeverFail_run_simulateQ_iff {spec : OracleSpec.{0,0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) :
    NeverFail (simulateQ (loggingOracle (spec := spec)) oa).run ↔ NeverFail oa := by
  rw [← probFailure_eq_zero_iff, ← probFailure_eq_zero_iff,
    HasEvalPMF.probFailure_eq_zero, HasEvalPMF.probFailure_eq_zero]

@[simp]
lemma probEvent_fst_run_simulateQ {spec : OracleSpec.{0,0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) (p : α → Prop) :
    Pr[fun z => p z.1 | (simulateQ (loggingOracle (spec := spec)) oa).run] = Pr[p | oa] := by
  rw [show (fun z : α × spec.QueryLog => p z.1) = p ∘ Prod.fst from rfl,
    ← probEvent_map, fst_map_run_simulateQ]

@[simp]
lemma probOutput_fst_map_run_simulateQ {spec : OracleSpec.{0,0} ι} {α : Type}
    [spec.Fintype] [spec.Inhabited]
    (oa : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (loggingOracle (spec := spec)) oa).run] =
      Pr[= x | oa] := by
  rw [fst_map_run_simulateQ]

end loggingOracle

/-- Add a query log to a computation using a logging oracle.  -/
@[reducible] def OracleComp.withQueryLog {α} (mx : OracleComp spec α) :
    OracleComp spec (α × QueryLog spec) :=
  WriterT.run (simulateQ (QueryImpl.ofLift spec (OracleComp spec)).withLogging mx)

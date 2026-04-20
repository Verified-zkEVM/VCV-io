/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.Structures
import VCVio.OracleComp.EvalDist
import ToMathlib.Control.Trace
import ToMathlib.Control.WriterT

/-!
# Generic Trace Instrumentation for Query Implementations

Two primitive ways to attach a writer-valued trace to a `QueryImpl`. Each
comes in two flavours, mirroring Mathlib's two `Monad (WriterT ω M)` instances:

* `[Monoid ω]` flavour (`withTrace` / `withTraceBefore`): the trace lives in
  an arbitrary monoid `ω` and accumulates via `1` and `*`. This is what
  `QueryImpl.withCost` (`CountingOracle.lean`) uses, with `ω = QueryCount ι`
  (pointwise additive monoid).

* `[EmptyCollection ω] [Append ω]` flavour (`withTraceAppend` /
  `withTraceAppendBefore`): the trace accumulates via `∅` and `++`, matching
  the Append-based `Monad (WriterT ω m)` instance. This is what
  `QueryImpl.withLogging` (`LoggingOracle.lean`) uses, with
  `ω = QueryLog spec` (a list of query/response pairs).

The two flavours are mathematically the same (a free monoid view vs. an
append-list view), but they correspond to *different* `Monad (WriterT ω m)`
instances and Lean's resolver picks whichever one is unambiguously available.
We expose both so neither of `QueryCount`/`QueryLog` has to switch its
underlying writer interpretation.

For each flavour, "Before" emits `traceFn t` *before* running the handler
(so a handler failure still records the trace), while the bare version emits
`traceFn t u` *after* the handler returns response `u` (so a failure skips
the trace).

Concretely:

* `withCost = withTraceBefore` (the cost ignores the response).
* `withLogging so = withTraceAppend so (fun t u => [⟨t, u⟩])` (the log records
  the response, hence "after" semantics).

The generic lemmas (output marginal, failure probability, `NeverFail`
equivalence, `evalDist` / `support` / `probOutput` bridges) flow downstream
automatically.

## Connection to `Control.Trace`

The trace function `traceFn : (t : spec.Domain) → spec.Range t → ω` is a curried
form of `Idx spec.toPFunctor → ω`, which is precisely
`Control.Trace ω (Idx spec.toPFunctor)`. The `Tracing` API is therefore the
oracle-level counterpart of the abstract `Control.Trace` / `PFunctor.Trace`
infrastructure in `ToMathlib`.
-/

open OracleSpec OracleComp

universe u v w

variable {ι : Type u} {spec : OracleSpec ι} {α β γ : Type u}

namespace QueryImpl

variable {m : Type u → Type v} [Monad m]

/-! ### `withTraceBefore`: response-independent trace, recorded before handler -/

section withTraceBefore

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records `traceFn t` in
the writer `ω` *before* running the handler. The trace value depends only on
the query, so a failure inside the handler still leaves the trace recorded. -/
def withTraceBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  fun t => do tell (traceFn t); so t

@[simp, grind =]
lemma withTraceBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withTraceBefore traceFn t = (do tell (traceFn t); so t) := rfl

lemma fst_map_run_withTraceBefore [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run = simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

/-- A "before"-style trace preserves failure probability for any base monad with
`HasEvalSPMF`: instrumenting with `withTraceBefore` does not change the
probability of failure. -/
lemma probFailure_run_simulateQ_withTraceBefore [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceBefore traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withTraceBefore traceFn) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withTraceBefore]

lemma NeverFail_run_simulateQ_withTraceBefore_iff [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceBefore traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withTraceBefore]

/-- When every query traces to the monoid identity `1`, `withTraceBefore` is a
no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTraceBefore_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTraceBefore (fun _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [ih]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceBefore` -/

lemma evalDist_fst_run_withTraceBefore [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    evalDist (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      evalDist (simulateQ so mx) :=
  congrArg evalDist (fst_map_run_withTraceBefore so traceFn mx)

lemma probOutput_fst_run_withTraceBefore [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceBefore]

lemma support_fst_run_withTraceBefore [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceBefore]

end withTraceBefore

/-! ### `withTrace`: response-dependent trace, recorded after handler -/

section withTrace

variable {ω : Type u} [Monoid ω]

/-- Wrap an oracle implementation so that each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`.
A handler failure skips the trace (the response never materialised). -/
def withTrace (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  fun t => do let u ← so t; tell (traceFn t u); return u

@[simp, grind =]
lemma withTrace_apply (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (t : spec.Domain) :
    so.withTrace traceFn t = (do let u ← so t; tell (traceFn t u); return u) := rfl

lemma fst_map_run_withTrace [LawfulMonad m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run = simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

/-- An "after"-style trace preserves failure probability for any base monad with
`HasEvalSPMF`: instrumenting with `withTrace` does not change the probability
of failure. When `m = OracleComp spec`, both sides are `0` (trivially true);
when `m` can genuinely fail (e.g. `OptionT (OracleComp spec)`), this is a
non-trivial faithfulness property. -/
lemma probFailure_run_simulateQ_withTrace [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTrace traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withTrace traceFn) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withTrace]

lemma NeverFail_run_simulateQ_withTrace_iff [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTrace traceFn) mx).run ↔ NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withTrace]

/-- When every query/response pair traces to the monoid identity `1`,
`withTrace` is a no-op up to pairing with `1`. -/
@[simp]
lemma run_simulateQ_withTrace_const_one [LawfulMonad m]
    (so : QueryImpl spec m) (mx : OracleComp spec α) :
    (simulateQ (so.withTrace (fun _ _ => (1 : ω))) mx).run =
      (·, 1) <$> simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih => simp [ih]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTrace` -/

lemma evalDist_fst_run_withTrace [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    evalDist (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      evalDist (simulateQ so mx) :=
  congrArg evalDist (fst_map_run_withTrace so traceFn mx)

lemma probOutput_fst_run_withTrace [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTrace]

lemma support_fst_run_withTrace [LawfulMonad m] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTrace traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTrace]

end withTrace

/-! ### `withTraceAppendBefore`: response-independent trace, recorded before
handler, accumulating via `∅` / `++` -/

section withTraceAppendBefore

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTraceBefore`: each query records
`traceFn t` in the writer `ω` *before* running the handler, and `WriterT`
uses the `[EmptyCollection ω] [Append ω]` `Monad` instance (`tell` is a single
push, `bind` concatenates with `++`). The trace value depends only on the
query, so a failure inside the handler still leaves the trace recorded. -/
def withTraceAppendBefore (so : QueryImpl spec m) (traceFn : spec.Domain → ω) :
    QueryImpl spec (WriterT ω m) :=
  fun t => do tell (traceFn t); so t

@[simp, grind =]
lemma withTraceAppendBefore_apply (so : QueryImpl spec m) (traceFn : spec.Domain → ω)
    (t : spec.Domain) :
    so.withTraceAppendBefore traceFn t = (do tell (traceFn t); so t) := rfl

lemma fst_map_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run = simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

lemma probFailure_run_simulateQ_withTraceAppendBefore [LawfulMonad m]
    [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withTraceAppendBefore]

lemma NeverFail_run_simulateQ_withTraceAppendBefore_iff [LawfulMonad m]
    [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppendBefore traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withTraceAppendBefore]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceAppendBefore` -/

lemma evalDist_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    evalDist (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      evalDist (simulateQ so mx) :=
  congrArg evalDist (fst_map_run_withTraceAppendBefore so traceFn mx)

lemma probOutput_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppendBefore]

lemma support_fst_run_withTraceAppendBefore [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : spec.Domain → ω) (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppendBefore traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppendBefore]

end withTraceAppendBefore

/-! ### `withTraceAppend`: response-dependent trace, recorded after handler,
accumulating via `∅` / `++` -/

section withTraceAppend

variable {ω : Type u} [EmptyCollection ω] [Append ω]

/-- Append-flavoured analogue of `withTrace`: each query records
`traceFn t u` in the writer `ω` *after* the handler returns response `u`,
using the `[EmptyCollection ω] [Append ω]` `Monad (WriterT ω m)` instance.
A handler failure skips the trace (the response never materialised). -/
def withTraceAppend (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) :
    QueryImpl spec (WriterT ω m) :=
  fun t => do let u ← so t; tell (traceFn t u); return u

@[simp, grind =]
lemma withTraceAppend_apply (so : QueryImpl spec m)
    (traceFn : (t : spec.Domain) → spec.Range t → ω) (t : spec.Domain) :
    so.withTraceAppend traceFn t = (do let u ← so t; tell (traceFn t u); return u) := rfl

lemma fst_map_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run = simulateQ so mx := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

lemma probFailure_run_simulateQ_withTraceAppend [LawfulMonad m]
    [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    Pr[⊥ | (simulateQ (so.withTraceAppend traceFn) mx).run] = Pr[⊥ | simulateQ so mx] := by
  rw [show Pr[⊥ | (simulateQ (so.withTraceAppend traceFn) mx).run] =
    Pr[⊥ | Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] from
    (probFailure_map _ _).symm, fst_map_run_withTraceAppend]

lemma NeverFail_run_simulateQ_withTraceAppend_iff [LawfulMonad m]
    [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    NeverFail (simulateQ (so.withTraceAppend traceFn) mx).run ↔
      NeverFail (simulateQ so mx) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_run_simulateQ_withTraceAppend]

/-! #### `evalDist` / `probOutput` / `support` bridges for `withTraceAppend` -/

lemma evalDist_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    evalDist (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      evalDist (simulateQ so mx) :=
  congrArg evalDist (fst_map_run_withTraceAppend so traceFn mx)

lemma probOutput_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) (x : α) :
    Pr[= x | Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run] =
      Pr[= x | simulateQ so mx] := by
  rw [fst_map_run_withTraceAppend]

lemma support_fst_run_withTraceAppend [LawfulMonad m] [LawfulAppend ω] [HasEvalSPMF m]
    (so : QueryImpl spec m) (traceFn : (t : spec.Domain) → spec.Range t → ω)
    (mx : OracleComp spec α) :
    support (Prod.fst <$> (simulateQ (so.withTraceAppend traceFn) mx).run) =
      support (simulateQ so mx) := by
  rw [fst_map_run_withTraceAppend]

end withTraceAppend

end QueryImpl

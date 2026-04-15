/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.Coercions.Add

/-!
# Observation Oracle for Side-Channel Leakage Modeling

This file defines an observation oracle that emits side-channel events during computation,
enabling formal reasoning about leakage properties such as constant-time execution and
distributional trace independence.

The core idea: model leakage instrumentation as an extra oracle family combined with the
original oracle spec via `+`. Observation events are accumulated in a `WriterT ω` layer,
reusing the `QueryImpl.withCost` infrastructure from `CountingOracle`.

## Main Definitions

* `ObsSpec Ev`: oracle spec where each event type `Ev` maps to a `PUnit` response.
* `observe`: emit an observation event into an instrumented computation.
* `eraseObs`: strip observation queries from a computation, recovering the base behavior.
* `runObs`: execute an observed computation, producing result paired with accumulated trace.

## Main Results

* `fst_map_runObs`: erasure theorem — projecting away the trace recovers `eraseObs`.
-/

open OracleSpec OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec ι} {Ev : Type u} {ω : Type u} {α β : Type u}

/-! ### Observation Spec -/

/-- Oracle spec for observation events: each event maps to a `PUnit` response.
Observation queries carry no computational payload and exist purely for
side-channel instrumentation. -/
abbrev ObsSpec (Ev : Type u) : OracleSpec Ev := fun _ => PUnit

/-- Emit an observation event into a computation with observation oracle access. -/
def observe (e : Ev) : OracleComp (spec + ObsSpec Ev) PUnit :=
  liftM (query (spec := ObsSpec Ev) e)

@[simp]
lemma observe_eq_liftM_query (e : Ev) :
    observe (spec := spec) e = liftM (query (spec := ObsSpec Ev) e) := rfl

/-! ### Erasure -/

/-- Oracle implementation that handles `spec + ObsSpec Ev` by forwarding base queries
and discarding observation events. -/
def eraseObsImpl : QueryImpl (spec + ObsSpec Ev) (OracleComp spec) :=
  fun t => match t with
  | .inl t => liftM (query (spec := spec) t)
  | .inr _ => pure PUnit.unit

@[simp, grind =]
lemma eraseObsImpl_inl (t : ι) :
    eraseObsImpl (spec := spec) (Ev := Ev) (.inl t) = liftM (query (spec := spec) t) := rfl

@[simp, grind =]
lemma eraseObsImpl_inr (e : Ev) :
    eraseObsImpl (spec := spec) (Sum.inr e) = (pure PUnit.unit : OracleComp spec PUnit) := rfl

/-- Strip observation queries from a computation, retaining only the base oracle queries.
All `observe` calls become no-ops; the functional behavior of the computation is preserved. -/
def eraseObs (oa : OracleComp (spec + ObsSpec Ev) α) : OracleComp spec α :=
  simulateQ eraseObsImpl oa

@[simp]
lemma eraseObs_pure (x : α) :
    eraseObs (spec := spec) (Ev := Ev) (pure x) = pure x := by
  simp [eraseObs]

@[simp]
lemma eraseObs_bind (oa : OracleComp (spec + ObsSpec Ev) α)
    (ob : α → OracleComp (spec + ObsSpec Ev) β) :
    eraseObs (oa >>= ob) = eraseObs oa >>= fun x => eraseObs (ob x) := by
  simp [eraseObs]

/-! ### Running Observed Computations -/

section runObs

variable [Monoid ω]

/-- Cost function for observation: base queries cost `1` (the monoid identity, so no trace
contribution), observation events cost `encode e`. -/
def obsCostFn (encode : Ev → ω) : (spec + ObsSpec Ev).Domain → ω :=
  fun t => match t with
  | .inl _ => 1
  | .inr e => encode e

/-- Execute an observed computation, producing the result paired with the accumulated
observation trace. Defined as `eraseObsImpl.withCost (obsCostFn encode)`, which reuses
the `QueryImpl.withCost` infrastructure. -/
def runObs (encode : Ev → ω) (oa : OracleComp (spec + ObsSpec Ev) α) :
    OracleComp spec (α × ω) :=
  (simulateQ (eraseObsImpl.withCost (obsCostFn encode)) oa).run

@[simp]
lemma runObs_pure (encode : Ev → ω) (x : α) :
    runObs (spec := spec) (Ev := Ev) encode (pure x) = pure (x, 1) := by
  simp [runObs]

/-- Erasure theorem: projecting away the observation trace recovers the erased computation.
This is the key compositionality property — adding observations does not change
the computation's functional behavior.

For failure preservation and `NeverFail` results in monads that can fail,
use `QueryImpl.probFailure_run_simulateQ_withCost` and
`QueryImpl.NeverFail_run_simulateQ_withCost_iff` applied to
`eraseObsImpl` and `obsCostFn` directly. These are trivial for `OracleComp`
since it has `HasEvalPMF`. -/
theorem fst_map_runObs (encode : Ev → ω) (oa : OracleComp (spec + ObsSpec Ev) α) :
    (fun z : α × ω => z.1) <$> runObs encode oa = eraseObs oa :=
  QueryImpl.fst_map_run_withCost eraseObsImpl (obsCostFn encode) oa

end runObs

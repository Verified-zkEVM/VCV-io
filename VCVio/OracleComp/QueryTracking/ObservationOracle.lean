/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.CountingOracle
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.HasQuery

/-!
# Observation Oracle for Side-Channel Leakage Modeling

This file defines an observation oracle that emits side-channel events during computation,
enabling formal reasoning about leakage properties such as constant-time execution and
distributional trace independence.

The API has two layers:

**Layer 1 (generic, `HasQuery`-based):** observation as a monad capability. Any monad `m` with
`HasQuery (ObsSpec Ev) m` can emit observation events. Two canonical `HasQuery` instances are
provided: `obsDiscard` (silently drops events) and `obsAccumulate` (accumulates events in a
`WriterT ω m` layer).

**Layer 2 (`simulateQ`-based):** for reinterpreting concrete `OracleComp (spec + ObsSpec Ev) α`
values. The definitions `eraseObs` and `runObs` are parameterized by a base oracle implementation
`base : QueryImpl spec m`, so they work for any target monad, not just `OracleComp spec`.

## Main Definitions

* `ObsSpec Ev`: oracle spec where each event type `Ev` maps to a `PUnit` response.
* `observe`: emit an observation event, generic over any `[HasQuery (ObsSpec Ev) m]`.
* `HasQuery.obsDiscard`: `HasQuery (ObsSpec Ev) m` instance that discards events.
* `HasQuery.obsAccumulate`: `HasQuery (ObsSpec Ev) (WriterT ω m)` instance that accumulates.
* `eraseObs`: strip observation queries via `simulateQ`, parameterized by base implementation.
* `runObs`: execute observed computation with trace accumulation, parameterized by base.

## Main Results

* `fst_map_runObs`: erasure theorem — projecting away the trace recovers `eraseObs`.
* `probFailure_runObs`: observations do not change failure probability (`[HasEvalSPMF m]`).
* `NeverFail_runObs_iff`: `NeverFail` is preserved by observation (`[HasEvalSPMF m]`).
-/

open OracleSpec OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec ι} {Ev : Type u} {ω : Type u} {α β : Type u}

/-! ### Observation Spec -/

/-- Oracle spec for observation events: each event maps to a `PUnit` response.
Observation queries carry no computational payload and exist purely for
side-channel instrumentation. -/
abbrev ObsSpec (Ev : Type u) : OracleSpec.{u, u} Ev := fun _ => PUnit.{u + 1}

/-! ### Layer 1: Generic HasQuery-Based Observation -/

section HasQueryObs

variable {m : Type u → Type*} [Monad m]

/-- Emit an observation event into any monad with observation query capability. -/
def observe [HasQuery (ObsSpec Ev) m] (e : Ev) : m PUnit :=
  HasQuery.query (spec := ObsSpec Ev) e

namespace HasQuery

/-- `HasQuery` instance that silently discards all observation events.
Use this to erase observations without changing the computation's behavior. -/
@[reducible]
def obsDiscard : HasQuery (ObsSpec Ev) m where
  query _ := pure PUnit.unit

/-- `HasQuery` instance that accumulates observation events in a `WriterT ω m` layer.
Each event `e` is encoded as `encode e` and accumulated via `tell`. -/
@[reducible]
def obsAccumulate [Monoid ω] (encode : Ev → ω) : HasQuery (ObsSpec Ev) (WriterT ω m) where
  query e := tell (encode e)

end HasQuery

end HasQueryObs

/-! ### Layer 2: SimulateQ-Based Erasure and Trace Collection -/

section SimulateQ

variable {m : Type u → Type*} [Monad m]

/-- Oracle implementation that handles `spec + ObsSpec Ev` by forwarding base queries to
`base` and discarding observation events. Parameterized by the base implementation so it
works for any target monad, not just `OracleComp spec`. -/
def eraseObsImpl (base : QueryImpl spec m) : QueryImpl (spec + ObsSpec Ev) m
  | .inl t => base t
  | .inr _ => pure PUnit.unit

@[simp, grind =]
lemma eraseObsImpl_inl (base : QueryImpl spec m) (t : ι) :
    eraseObsImpl (Ev := Ev) base (.inl t) = base t := rfl

@[simp, grind =]
lemma eraseObsImpl_inr (base : QueryImpl spec m) (e : Ev) :
    eraseObsImpl base (.inr e) = (pure PUnit.unit : m PUnit) := rfl

/-- Strip observation queries from a computation, retaining only the base oracle queries.
All `observe` calls become no-ops; the functional behavior of the computation is preserved. -/
def eraseObs (base : QueryImpl spec m) (oa : OracleComp (spec + ObsSpec Ev) α) : m α :=
  simulateQ (eraseObsImpl base) oa

@[simp]
lemma eraseObs_pure (base : QueryImpl spec m) (x : α) :
    eraseObs (Ev := Ev) base (pure x) = pure x := by
  simp [eraseObs]

@[simp]
lemma eraseObs_bind [LawfulMonad m] (base : QueryImpl spec m)
    (oa : OracleComp (spec + ObsSpec Ev) α)
    (ob : α → OracleComp (spec + ObsSpec Ev) β) :
    eraseObs base (oa >>= ob) = eraseObs base oa >>= fun x => eraseObs base (ob x) := by
  simp [eraseObs]

/-! ### Running Observed Computations -/

section runObs

variable [Monoid ω]

/-- Cost function for observation: base queries cost `1` (the monoid identity, so no trace
contribution), observation events cost `encode e`. -/
def obsCostFn (encode : Ev → ω) : (spec + ObsSpec Ev).Domain → ω
  | .inl _ => 1
  | .inr e => encode e

/-- Execute an observed computation, producing the result paired with the accumulated
observation trace. Parameterized by a base oracle implementation `base : QueryImpl spec m`,
so this works for any target monad. -/
def runObs (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) : m (α × ω) :=
  (simulateQ ((eraseObsImpl base).withCost (obsCostFn encode)) oa).run

@[simp]
lemma runObs_pure (base : QueryImpl spec m) (encode : Ev → ω) (x : α) :
    runObs base encode (pure x) = pure (x, 1) := by
  simp [runObs]

/-- Erasure theorem: projecting away the observation trace recovers the erased computation. -/
theorem fst_map_runObs [LawfulMonad m] (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) :
    (fun z : α × ω => z.1) <$> runObs base encode oa = eraseObs base oa := by
  change Prod.fst <$> (simulateQ ((eraseObsImpl base).withCost (obsCostFn encode)) oa).run =
    simulateQ (eraseObsImpl base) oa
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa h => simp [h]

/-- Failure preservation: observations do not change the probability of failure. -/
theorem probFailure_runObs [LawfulMonad m] [HasEvalSPMF m]
    (base : QueryImpl spec m) (encode : Ev → ω) (oa : OracleComp (spec + ObsSpec Ev) α) :
    Pr[⊥ | runObs base encode oa] = Pr[⊥ | eraseObs base oa] := by
  rw [show Pr[⊥ | runObs base encode oa] =
    Pr[⊥ | (fun z : α × ω => z.1) <$> runObs base encode oa] from
    (probFailure_map _ _).symm, fst_map_runObs]

/-- `NeverFail` is preserved by observation. -/
theorem NeverFail_runObs_iff [LawfulMonad m] [HasEvalSPMF m]
    (base : QueryImpl spec m) (encode : Ev → ω) (oa : OracleComp (spec + ObsSpec Ev) α) :
    NeverFail (runObs base encode oa) ↔ NeverFail (eraseObs base oa) := by
  simp only [HasEvalSPMF.neverFail_iff, probFailure_runObs]

/-! ### EvalDist Bridge for `runObs`

These lemmas connect the result-marginal distribution of `runObs` to the distribution
of `eraseObs`, enabling direct probability-level reasoning about traces without needing
to manually simplify the traced computation into its concrete form. -/

lemma evalDist_fst_runObs [LawfulMonad m] [HasEvalSPMF m]
    (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) :
    evalDist ((fun z : α × ω => z.1) <$> runObs base encode oa) =
      evalDist (eraseObs base oa) := by
  rw [fst_map_runObs]

lemma probOutput_fst_runObs [LawfulMonad m] [HasEvalSPMF m]
    (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) (x : α) :
    Pr[= x | (fun z : α × ω => z.1) <$> runObs base encode oa] =
      Pr[= x | eraseObs base oa] := by
  rw [fst_map_runObs]

lemma support_fst_runObs [LawfulMonad m] [HasEvalSPMF m]
    (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) :
    support ((fun z : α × ω => z.1) <$> runObs base encode oa) =
      support (eraseObs base oa) := by
  rw [fst_map_runObs]

/-! ### Structural Lemmas for `runObs` -/

@[simp]
lemma runObs_bind [LawfulMonad m] (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) (ob : α → OracleComp (spec + ObsSpec Ev) β) :
    runObs base encode (oa >>= ob) = do
      let ⟨a, w₁⟩ ← runObs base encode oa
      let ⟨b, w₂⟩ ← runObs base encode (ob a)
      return (b, w₁ * w₂) := by
  simp only [runObs, simulateQ_bind, WriterT.run_bind]
  congr 1; ext ⟨a, w₁⟩
  simp

@[simp]
lemma runObs_map [LawfulMonad m] (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp (spec + ObsSpec Ev) α) (f : α → β) :
    runObs base encode (f <$> oa) = Prod.map f id <$> runObs base encode oa := by
  simp only [runObs, simulateQ_map, WriterT.run_map']

/-- `runObs` on a single base-spec query lifted into `spec + ObsSpec Ev`: the trace is `1`. -/
@[simp]
lemma runObs_liftM_query_inl [LawfulMonad m] (base : QueryImpl spec m)
    (encode : Ev → ω) (t : spec.Domain) :
    runObs base encode ((liftM (query t : OracleQuery spec _) :
        OracleComp (spec + ObsSpec Ev) _)) = (·, 1) <$> base t := by
  change (simulateQ ((eraseObsImpl base).withCost (obsCostFn encode))
    (liftM (liftM (query t : OracleQuery spec _) :
      OracleQuery (spec + ObsSpec Ev) _))).run = _
  simp [QueryImpl.withCost, eraseObsImpl, obsCostFn]

/-- `runObs` on a lifted base-spec computation: the trace is `1` (monoid identity). -/
@[simp]
lemma runObs_liftComp [LawfulMonad m] (base : QueryImpl spec m) (encode : Ev → ω)
    (oa : OracleComp spec α) :
    runObs base encode ((liftM oa : OracleComp (spec + ObsSpec Ev) α)) =
      (·, 1) <$> simulateQ base oa := by
  change runObs base encode (liftComp oa (spec + ObsSpec Ev)) = _
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t oa ih =>
    simp only [liftComp_bind, liftComp_query, OracleQuery.cont_query,
      id_map, OracleQuery.input_query, runObs_bind, runObs_liftM_query_inl,
      simulateQ_bind, simulateQ_query, map_bind, bind_map_left, ih]
    simp

/-- `runObs` on `observe e`: the result is `PUnit.unit` with trace `encode e`. -/
@[simp]
lemma runObs_observe [LawfulMonad m] (base : QueryImpl spec m) (encode : Ev → ω) (e : Ev) :
    runObs base encode (observe (Ev := Ev) e :
        OracleComp (spec + ObsSpec Ev) PUnit) =
      pure (PUnit.unit, encode e) := by
  change (simulateQ ((eraseObsImpl base).withCost (obsCostFn encode))
    (liftM (liftM (query e : OracleQuery (ObsSpec Ev) _) :
      OracleQuery (spec + ObsSpec Ev) _))).run = _
  simp [QueryImpl.withCost, eraseObsImpl, obsCostFn]

end runObs

end SimulateQ

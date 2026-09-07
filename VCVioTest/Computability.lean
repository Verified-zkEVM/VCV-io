/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import VCVio

/-!
# Computability Regression Test

Compile-time lock on the computability of the oracle-simulation and replay-fork pipeline.
Every declaration below is a plain `def`: the test is that each one elaborates *without*
`noncomputable`, so code generation succeeds for the whole pipeline. If a refactor
accidentally makes any ingredient noncomputable (e.g. by routing a program-layer definition
through `PMF`, `Classical.decEq`, or `Fintype.ofFinite`), this file fails to compile.

The dividing line this file locks is: *programs* (`OracleComp` values, `QueryImpl` handlers,
`StateT`/`WriterT` simulators, `ProbComp` runs) are computable, while *semantics*
(`evalSPMF`, `Pr[⋯]`, `SPMF`, expected costs) remain noncomputable. Executability lets
library users smoke-test security reductions by actually running them via
`OracleComp.runIO`, turning "efficient by inspection" into inspection plus execution.

No `#eval` is used: outputs are random, so any runtime assertion would be flaky. The lock
is compilation itself.
-/

public section

open OracleComp OracleSpec

namespace VCVioTest.Computability

/-! ## Lazy random-oracle simulation pipeline

Locks `unifFwdImpl`, `randomOracle`, and their sum: the standard interpretation of a
`unifSpec + hashSpec` computation into `StateT QueryCache ProbComp`. -/

/-- The lazy-RO simulation pipeline used throughout the Fiat-Shamir and Fischlin layers. -/
def roSimPipeline :
    QueryImpl (unifSpec + (ℕ →ₒ Bool))
      (StateT ((ℕ →ₒ Bool) : OracleSpec ℕ).QueryCache ProbComp) :=
  unifFwdImpl (ℕ →ₒ Bool) +
    (randomOracle : QueryImpl ((ℕ →ₒ Bool) : OracleSpec ℕ) _)

/-- A toy random-oracle computation: query two hash points and combine the answers. -/
def roToy : OracleComp (unifSpec + (ℕ →ₒ Bool)) Bool := do
  let b₁ ← (unifSpec + (ℕ →ₒ Bool)).query (Sum.inr 0)
  let b₂ ← (unifSpec + (ℕ →ₒ Bool)).query (Sum.inr 1)
  pure (b₁ != b₂)

/-- The toy computation run through the pipeline from the empty cache, as a `ProbComp`. -/
def roToyProb : ProbComp Bool :=
  (simulateQ roSimPipeline roToy).run' ∅

/-- A mixed toy computation that makes both a fresh uniform query and a hash query. -/
def roMixedToy : OracleComp (unifSpec + (ℕ →ₒ Bool)) Bool := do
  let coin : Fin 2 ← (unifSpec + (ℕ →ₒ Bool)).query (Sum.inl 1)
  let hash ← (unifSpec + (ℕ →ₒ Bool)).query (Sum.inr 0)
  pure ((coin == 0) == hash)

/-- The fixed-hash-table interpretation remains computable while forwarding uniform queries. -/
def roMixedFixed (f : QueryImpl ((ℕ →ₒ Bool) : OracleSpec ℕ) Id) : ProbComp Bool :=
  simulateQ (OracleComp.unifFwdAnswerImpl f) roMixedToy

/-- API canary for the probability-one bridge on a computation containing both query kinds. -/
example (p : Bool → Prop) :
    Pr[fun v => p v.1 | (simulateQ roSimPipeline roMixedToy).run
      (∅ : ((ℕ →ₒ Bool) : OracleSpec ℕ).QueryCache)] = 1
    ↔
    ∀ f : QueryImpl ((ℕ →ₒ Bool) : OracleSpec ℕ) Id,
      (∅ : ((ℕ →ₒ Bool) : OracleSpec ℕ).QueryCache).AgreesWithFn f →
        Pr[p | roMixedFixed f] = 1 := by
  simpa only [roSimPipeline, roMixedFixed] using
    (OracleComp.probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff
      (oa := roMixedToy) (preexisting_cache :=
        (∅ : ((ℕ →ₒ Bool) : OracleSpec ℕ).QueryCache)) p)

/-! ## Replay fork

Locks `contextFork` and `contextForkCollision` on a minimal main computation, plus their
interpretation down to `ProbComp` (via `uniformSampleImpl`) and `IO` (via `runIO`). -/

/-- A minimal forkable main computation: one focused oracle query. -/
def toyMain : OracleComp (unifSpec + (Unit →ₒ Bool)) Bool := do
  let b ← (unifSpec + (Unit →ₒ Bool)).query (Sum.inr ())
  pure b

/-- Query budget for `toyMain`: one query at the focused index, none elsewhere. -/
def toyBudget : ℕ ⊕ Unit → ℕ
  | .inl _ => 0
  | .inr () => 1

/-- The replay fork of `toyMain` at the focused query. -/
def toyFork : OracleComp (unifSpec + (Unit →ₒ Bool)) (Option (Bool × Bool)) :=
  contextFork toyMain toyBudget (Sum.inr ()) (fun b => if b then some 0 else none)

/-- The collision branch of the replay fork on `toyMain`. -/
def toyForkCollision : OracleComp (unifSpec + (Unit →ₒ Bool)) (Option (Fin 2)) :=
  contextForkCollision toyMain toyBudget (Sum.inr ())
    (fun b => if b then some 0 else none) 0

/-- The replay fork interpreted into `ProbComp` by uniform sampling. -/
def toyForkProb : ProbComp (Option (Bool × Bool)) :=
  simulateQ (QueryImpl.ofLift unifSpec ProbComp +
    uniformSampleImpl (spec := ((Unit →ₒ Bool) : OracleSpec Unit))) toyFork

/-- The replay fork as an executable `IO` action. -/
def toyForkIO : IO (Option (Bool × Bool)) :=
  OracleComp.runIO toyForkProb

/-! ## Base-monad mapping combinators

Locks `QueryImpl.mapStateTBase` and `QueryImpl.writerTMapBase`, the combinators that push an
outer interpreter through a stateful or logging handler. -/

/-- A stateful handler over `ProbComp` that records each sampled answer. -/
def toyTrackingInner : QueryImpl (Unit →ₒ Bool) (StateT (List Bool) ProbComp) :=
  fun (_ : Unit) => do
    let b ← liftM ($ᵗ Bool)
    modifyGet fun log => (b, b :: log)

/-- `toyTrackingInner` with its base `ProbComp` mapped through the identity forwarder. -/
def toyMappedState : QueryImpl (Unit →ₒ Bool) (StateT (List Bool) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).mapStateTBase toyTrackingInner

/-- A logging handler with its base `ProbComp` mapped through the identity forwarder. -/
def toyMappedWriter :
    QueryImpl (Unit →ₒ Bool)
      (WriterT (QueryLog ((Unit →ₒ Bool) : OracleSpec Unit)) ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).writerTMapBase
    (uniformSampleImpl (spec := ((Unit →ₒ Bool) : OracleSpec Unit))).withLogging

end VCVioTest.Computability

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.Interaction.UC.Computational

/-!
# Runtime execution semantics for open processes

This file bridges the structural `OpenProcess` layer to probabilistic
computation (`ProbComp`) by defining how to execute a closed process.

The core runtime primitives (`Spec.Sampler`, `sampleTranscript`,
`StepOver.sample`, `ProcessOver.runSteps`) are parameterized by an
arbitrary monad `m : Type → Type`. This generality lets the execution
intermediate monad carry oracle access (random oracles, CRS, etc.)
shared across all parties. The `processSemantics` constructor then
takes a closing morphism `m Unit → ProbComp Unit` that resolves the
intermediate monad into the denotational target.

Common instantiations:

* `m = ProbComp`, `close = id`: coin-flip-only protocols.
  Use `processSemanticsProbComp`.

* `m = OracleComp (unifSpec + roSpec)`,
  `close = fun mx => (simulateQ impl mx).run' ∅`:
  protocols in the random oracle model, where `impl` combines a
  `unifSpec` identity lift with `randomOracle` (or any `QueryImpl`).
  Use `processSemanticsOracle`.

## Main definitions

* `Spec.Sampler m spec` provides an `m X` computation at each node of
  a `Spec` tree, resolving each move in the intermediate monad.

* `Spec.sampleTranscript` executes a sampler to produce a full transcript
  in `m`.

* `StepOver.sample` runs one step by sampling a transcript and applying
  the continuation.

* `ProcessOver.runSteps` iterates `sample` for a fixed number of steps.

* `UC.processSemantics` constructs a `Semantics (openTheory Party)` from
  a closing morphism, initial state, step sampler, fuel count, and
  observation function.

* `UC.processSemanticsProbComp` is the specialization for `m = ProbComp`.

* `UC.processSemanticsOracle` constructs semantics for protocols with
  shared oracle access, using `simulateQ` to close.

## Universe constraints

The runtime layer requires the spec and state type universes to be `0`,
since `ProbComp : Type → Type` operates in `Type`. This is satisfied by
concrete protocols whose move types and state types live in `Type`.
-/

universe u

open OracleComp

namespace Interaction

namespace Spec

/--
A `Sampler` for `spec : Spec.{0}` provides an `m X` computation at each
node whose move space is `X`, plus recursive samplers for every subtree.

The monad `m` is the intermediate execution monad. Typical choices:
* `ProbComp` for coin-flip-only protocols.
* `OracleComp (unifSpec + roSpec)` for protocols with shared random oracle
  access, where samplers can issue oracle queries via `query`.
-/
def Sampler (m : Type → Type) : Spec.{0} → Type
  | .done => PUnit
  | .node X rest => m X × (∀ x, Sampler m (rest x))

/--
Execute a sampler to produce a full transcript of `spec` in the monad `m`.

At each node the sampler monadically chooses a move; that move determines
which subtree to continue sampling.
-/
noncomputable def sampleTranscript {m : Type → Type} [Monad m] :
    (spec : Spec.{0}) → Sampler m spec → m (Transcript spec)
  | .done, _ => pure ⟨⟩
  | .node _ rest, ⟨samp, sampRest⟩ => do
      let x ← samp
      let tr ← sampleTranscript (rest x) (sampRest x)
      return ⟨x, tr⟩

end Spec

namespace Concurrent

/--
Run one step of a `ProcessOver` by sampling a transcript from the step's
spec and applying the continuation to get the next state.
-/
noncomputable def StepOver.sample {m : Type → Type} [Monad m]
    {Γ : Spec.Node.Context} {P : Type}
    (step : StepOver Γ P) (sampler : Spec.Sampler m step.spec) : m P := do
  let tr ← Spec.sampleTranscript step.spec sampler
  return step.next tr

/--
Run `fuel` steps of a process, starting from state `s`, using a
state-dependent sampler at each step.
-/
noncomputable def ProcessOver.runSteps {m : Type → Type} [Monad m]
    {Γ : Spec.Node.Context}
    (process : ProcessOver Γ)
    (sampler : (p : process.Proc) → Spec.Sampler m (process.step p).spec) :
    ℕ → process.Proc → m process.Proc
  | 0, s => pure s
  | n + 1, s => do
    let s' ← (process.step s).sample (sampler s)
    runSteps process sampler n s'

end Concurrent

namespace UC

open Concurrent

private abbrev Closed (Party : Type u) :=
  (openTheory.{u, 0, 0} Party).Closed

/--
Construct a `Semantics` for the open-process theory, parameterized by an
intermediate execution monad `m` and a closing morphism `close`.

The execution runs entirely in `m`: the sampler produces moves, multi-step
iteration threads them, and the observer extracts the final judgment.
The closing morphism `close : m Unit → ProbComp Unit` then maps the
whole execution into `ProbComp Unit` for the computational observation
layer.

See `processSemanticsProbComp` for the coin-flip-only specialization and
`processSemanticsOracle` for the shared-oracle specialization.
-/
noncomputable def processSemantics (Party : Type u)
    {m : Type → Type} [Monad m]
    (close : m Unit → ProbComp Unit)
    (init : ∀ (p : Closed Party), p.Proc)
    (sampler : ∀ (p : Closed Party) (s : p.Proc),
      Spec.Sampler m (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party), p.Proc → m Unit) :
    Semantics (openTheory.{u, 0, 0} Party) where
  run process :=
    close (do
      let finalState ← process.runSteps (sampler process) fuel (init process)
      observe process finalState)

/--
`processSemanticsProbComp` is the specialization of `processSemantics` for
`m = ProbComp` (coin-flip-only protocols with no shared oracles).
-/
noncomputable def processSemanticsProbComp (Party : Type u)
    (init : ∀ (p : Closed Party), p.Proc)
    (sampler : ∀ (p : Closed Party) (s : p.Proc),
      Spec.Sampler ProbComp (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party), p.Proc → ProbComp Unit) :
    Semantics (openTheory.{u, 0, 0} Party) :=
  processSemantics Party id init sampler fuel observe

/--
`processSemanticsOracle` constructs semantics for protocols with shared
oracle access (random oracles, CRS, etc.).

The intermediate monad is `OracleComp superSpec`, where `superSpec`
describes all oracles available during execution. Oracle queries are
resolved by `simulateQ impl` into `StateT σ ProbComp`, and the oracle
state is initialized to `initOracle`.

For a protocol in the random oracle model, a typical instantiation is:
* `superSpec := unifSpec + (D →ₒ R)` (uniform sampling plus hash oracle)
* `impl := HasQuery.toQueryImpl.liftTarget _ + randomOracle`
  (identity on `unifSpec`, lazy-cached on the hash)
* `initOracle := ∅` (empty random oracle cache)
-/
noncomputable def processSemanticsOracle (Party : Type u)
    {ι : Type} {superSpec : OracleSpec.{0, 0} ι} {σ : Type}
    (impl : QueryImpl superSpec (StateT σ ProbComp))
    (initOracle : σ)
    (init : ∀ (p : Closed Party), p.Proc)
    (sampler : ∀ (p : Closed Party) (s : p.Proc),
      Spec.Sampler (OracleComp superSpec) (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party), p.Proc → OracleComp superSpec Unit) :
    Semantics (openTheory.{u, 0, 0} Party) :=
  processSemantics Party
    (m := OracleComp superSpec)
    (close := fun mx => (simulateQ impl mx).run' initOracle)
    init sampler fuel observe

end UC
end Interaction

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.Interaction.UC.Computational

/-!
# Runtime execution semantics for open processes

This file bridges the structural `OpenProcess` layer to the bundled
sub-probabilistic semantics (`UC.Semantics`) by defining how to execute
a closed process.

The core runtime primitives (`Spec.Sampler`, `sampleTranscript`,
`StepOver.sample`, `ProcessOver.runSteps`) are parameterized by an
arbitrary monad `m : Type → Type`. This generality lets the execution
intermediate monad carry additional capabilities, such as shared oracle
access (random oracles, CRS, …), while the bundled
`SPMFSemantics m` fixes how those capabilities are collapsed into the
externally visible `SPMF Unit`.

Common instantiations:

* `m = ProbComp` with `sem := SPMFSemantics.ofHasEvalSPMF ProbComp` for
  coin-flip-only protocols. Use `processSemanticsProbComp`.

* `m = OracleComp (unifSpec + roSpec)` with a hand-rolled
  `SPMFSemantics` whose internal monad is `StateT σ ProbComp` and whose
  interpreter is `simulateQ' impl`. Use `processSemanticsOracle` for
  protocols in the random oracle model, where `impl` combines a
  `unifSpec` identity lift with `randomOracle` (or any `QueryImpl`).

* Observation-style semantics that deliberately carry failure mass,
  for example `m = OptionT ProbComp` with
  `SPMFSemantics.ofHasEvalSPMF (OptionT ProbComp)`. This is what
  cryptographic smoke tests (OTP-style privacy, guess games) use to
  produce a non-vacuous `CompEmulates 0` discharge.

## Main definitions

* `Spec.Sampler m spec` provides an `m X` computation at each node of
  a `Spec` tree, resolving each move in the intermediate monad.

* `Spec.sampleTranscript` executes a sampler to produce a full
  transcript in `m`.

* `StepOver.sample` runs one step by sampling a transcript and applying
  the continuation.

* `ProcessOver.runSteps` iterates `sample` for a fixed number of steps.

* `UC.processSemantics` constructs a `Semantics (openTheory Party)`
  from a bundled `SPMFSemantics m`, an initial state, a step sampler,
  a fuel count, and an observation function. The resulting semantics
  observes closed systems through `sem.evalDist`.

* `UC.processSemanticsProbComp` is the specialization for `m =
  ProbComp` with its canonical `SPMFSemantics`.

* `UC.processSemanticsOracle` constructs semantics for protocols with
  shared oracle access, collapsing the oracle layer through
  `simulateQ'`.

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

Structurally this is exactly a `Spec.Decoration` whose node context is
`fun X => m X`: the per-node decoration stores an `m`-computation in
the move type of that node, and the functorial `Decoration.map` /
`Decoration.map_id` / `Decoration.map_comp` API applies immediately.

The monad `m` is the intermediate execution monad. Typical choices:
* `ProbComp` for coin-flip-only protocols.
* `OracleComp (unifSpec + roSpec)` for protocols with shared random oracle
  access, where samplers can issue oracle queries via `query`.
* `OptionT ProbComp` for observation-style semantics that need to
  inject failure mass.
-/
abbrev Sampler (m : Type → Type) (spec : Spec.{0}) : Type :=
  Decoration (fun X => m X) spec

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
Construct a `Semantics` for the open-process theory, parameterized by a
surface execution monad `m` together with a bundled `SPMFSemantics m`.

The execution runs entirely in `m`: the sampler produces moves,
multi-step iteration threads them, and the observer extracts the final
judgment as a `m Unit` value. The bundled `sem` then collapses the
`m Unit` game into a `SPMF Unit` via
`Semantics.evalDist`.

See `processSemanticsProbComp` for the coin-flip-only specialization
and `processSemanticsOracle` for the shared-oracle specialization.
-/
noncomputable def processSemantics (Party : Type u)
    {m : Type → Type} [Monad m]
    (sem : SPMFSemantics.{0, 0, 0} m)
    (init : ∀ (p : Closed Party), p.Proc)
    (sampler : ∀ (p : Closed Party) (s : p.Proc),
      Spec.Sampler m (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party), p.Proc → m Unit) :
    Semantics (openTheory.{u, 0, 0} Party) where
  m := m
  instMonad := inferInstance
  sem := sem
  run process := do
    let finalState ← process.runSteps (sampler process) fuel (init process)
    observe process finalState

/--
`processSemanticsProbComp` is the specialization of `processSemantics`
for `m = ProbComp` with its canonical `SPMFSemantics`
(`SPMFSemantics.ofHasEvalSPMF`).
This is the right entry point for coin-flip-only protocols with no
shared oracles and no deliberate failure mass.
-/
noncomputable def processSemanticsProbComp (Party : Type u)
    (init : ∀ (p : Closed Party), p.Proc)
    (sampler : ∀ (p : Closed Party) (s : p.Proc),
      Spec.Sampler ProbComp (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party), p.Proc → ProbComp Unit) :
    Semantics (openTheory.{u, 0, 0} Party) :=
  processSemantics Party (SPMFSemantics.ofHasEvalSPMF ProbComp)
    init sampler fuel observe

/--
`processSemanticsOracle` constructs semantics for protocols with shared
oracle access (random oracles, CRS, etc.).

The surface monad is `OracleComp superSpec`, where `superSpec` describes
all oracles available during execution. The bundled `SPMFSemantics`
interprets those oracle queries by `simulateQ' impl` into
`StateT σ ProbComp`, initializing the oracle state to `initOracle` and
projecting onto the output to obtain the final `SPMF Unit`.

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
  let oracleSem : SPMFSemantics.{0, 0, 0} (OracleComp superSpec) :=
    { Sem := StateT σ ProbComp
      instMonadSem := inferInstance
      interpret := simulateQ' impl
      observe := fun {_} mx => HasEvalSPMF.toSPMF (mx.run' initOracle) }
  processSemantics Party (m := OracleComp superSpec) oracleSem
    init sampler fuel observe

end UC
end Interaction

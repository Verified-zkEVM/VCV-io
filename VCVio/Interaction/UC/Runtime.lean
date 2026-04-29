/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.Basic.Sampler
import VCVio.Interaction.Basic.SpecFintype
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.Interaction.UC.Computational
import VCVio.OracleComp.Constructions.SampleableType

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
  cryptographic smoke tests (OTP-style privacy, guess games) use so
  that the `guard` branch contributes a real failure mass to the
  resulting `SPMF Unit`.

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
Uniform selection from a nonempty finite type as a `ProbComp` primitive,
realized by reducing to uniform selection on `Fin (Fintype.card X)` via the
classical equivalence `Fintype.equivFin`. This is the tree-node analogue of
`PMF.uniformOfFintype`, landing in `ProbComp` so that it can be plugged
directly into per-node components of a `Sampler ProbComp spec`.
-/
noncomputable def probCompUniformOfFintype
    (X : Type) [Fintype X] [Nonempty X] : ProbComp X :=
  haveI : NeZero (Fintype.card X) := ⟨Fintype.card_ne_zero⟩
  (Fintype.equivFin X).symm <$> ($ᵗ Fin (Fintype.card X))

/--
Canonical uniform sampler on a `Spec.Fintype`-ornamented spec, built by
recursion on the ornament: each node samples uniformly from its move
space using `probCompUniformOfFintype`, and the continuation samplers
are produced recursively from the per-branch ornament.

This is the interaction-spec analogue of `SampleableType` for
`OracleSpec`: concrete `spec` trees whose move types all carry `Fintype`
and `Nonempty` synthesize an instance of `Spec.Fintype spec`
automatically, yielding `Sampler.uniform spec` as the canonical
coin-flip-only sampler for downstream runtime semantics
(`processSemanticsProbComp`, etc.).
-/
noncomputable def Sampler.uniform :
    (spec : Spec.{0}) → Spec.Fintype spec → Sampler ProbComp spec
  | .done, _ => ⟨⟩
  | .node X rest, .node hFin hNon hRec =>
      haveI := hFin
      haveI := hNon
      (probCompUniformOfFintype X,
        fun x => Sampler.uniform (rest x) (hRec x))

/-- Instance-argument form of `Sampler.uniform`. -/
@[reducible]
noncomputable def Sampler.uniformI (spec : Spec.{0}) [h : Spec.Fintype spec] :
    Sampler ProbComp spec :=
  Sampler.uniform spec h

/-! Smoke test: typeclass synthesis builds a `Spec.Fintype` instance for a
concrete spec, and `Sampler.uniformI` elaborates against it. -/

private example : Spec.Fintype
    (Spec.node Bool (fun _ => Spec.node (Fin 4) (fun _ => Spec.done))) :=
  inferInstance

private noncomputable example :
    Sampler ProbComp
      (Spec.node Bool (fun _ => Spec.node (Fin 4) (fun _ => Spec.done))) :=
  Sampler.uniformI _

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

private abbrev Closed (Party : Type u) (m : Type → Type)
    (schedulerSampler : m (ULift Bool)) :=
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Closed

/--
Construct a `Semantics` for the open-process theory, parameterized by a
surface execution monad `m` together with a bundled `SPMFSemantics m`.

The execution runs entirely in `m`: per-step samplers come from the
`OpenProcess`'s `stepSampler` field, multi-step iteration threads them,
and the observer extracts the final judgment as an `m Unit` value. The
bundled `sem` then collapses the `m Unit` game into a `SPMF Unit` via
`Semantics.evalDist`.

See `processSemanticsProbComp` for the coin-flip-only specialization
and `processSemanticsOracle` for the shared-oracle specialization.
-/
noncomputable def processSemantics (Party : Type u)
    {m : Type → Type} [Monad m]
    (schedulerSampler : m (ULift Bool))
    (sem : SPMFSemantics.{0, 0, 0} m)
    (init : ∀ (p : Closed Party m schedulerSampler), p.Proc)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party m schedulerSampler), p.Proc → m Unit) :
    Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler) where
  m := m
  instMonad := inferInstance
  sem := sem
  run process := do
    let finalState ←
      process.toProcess.runSteps process.stepSampler fuel (init process)
    observe process finalState

/--
`processSemanticsProbComp` is the specialization of `processSemantics`
for `m = ProbComp` with its canonical `SPMFSemantics`
(`SPMFSemantics.ofHasEvalSPMF`).
This is the right entry point for coin-flip-only protocols with no
shared oracles and no deliberate failure mass.
-/
noncomputable def processSemanticsProbComp (Party : Type u)
    (schedulerSampler : ProbComp (ULift Bool))
    (init : ∀ (p : Closed Party ProbComp schedulerSampler), p.Proc)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party ProbComp schedulerSampler),
      p.Proc → ProbComp Unit) :
    Semantics (openTheory.{u, 0, 0, 0} Party ProbComp schedulerSampler) :=
  processSemantics Party schedulerSampler (SPMFSemantics.ofHasEvalSPMF ProbComp)
    init fuel observe

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
    (schedulerSampler : OracleComp superSpec (ULift Bool))
    (impl : QueryImpl superSpec (StateT σ ProbComp))
    (initOracle : σ)
    (init : ∀ (p : Closed Party (OracleComp superSpec) schedulerSampler),
      p.Proc)
    (fuel : ℕ)
    (observe : ∀ (p : Closed Party (OracleComp superSpec) schedulerSampler),
      p.Proc → OracleComp superSpec Unit) :
    Semantics
      (openTheory.{u, 0, 0, 0} Party (OracleComp superSpec) schedulerSampler) :=
  let oracleSem : SPMFSemantics.{0, 0, 0} (OracleComp superSpec) :=
    { Sem := StateT σ ProbComp
      instMonadSem := inferInstance
      interpret := simulateQ' impl
      observe := fun {_} mx => HasEvalSPMF.toSPMF (mx.run' initOracle) }
  processSemantics Party (m := OracleComp superSpec) schedulerSampler oracleSem
    init fuel observe

end UC
end Interaction

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.AsyncRuntime
import VCVio.Interaction.UC.OpenProcessModel

/-!
# Sync-recovery demo for the asynchronous runtime

This file exhibits `processSemantics_eq_processSemanticsAsync_trivial`
(and its `ProbComp` specialization) on a fully concrete closed-Party
value, confirming end-to-end that the trivial async semantics is
provably equal to the synchronous semantics on real input.

The closed system used here is `openTheory_unit Party` with
`Party := Unit`: the single-party trivial process whose every step is
`.done`. This is the smallest object in the closed-Party theory of
`openTheory`, and it suffices to validate two things about the
recovery API:

* **Semantics-level equality.** The synchronous `processSemanticsProbComp`
  and the trivial-env-scheduler async lift built from
  `processSemanticsAsyncProbComp` are equal *as `Semantics` values*,
  for every choice of `init`, `sampler`, `fuel`, and `observe`.

* **Pointwise equality on a concrete process.** Specializing both
  semantics to the concrete `trivialClosed : Closed Unit` value and
  unfolding the recovery rewrite produces equal `ProbComp Unit`
  computations.

Larger ports (e.g. wrapping a `MachineProcess` against the canonical
momentary-corruption env channel as in `Examples/Corruption/AKE.lean`)
follow the same pattern: build the sync semantics, build the async
semantics via the corresponding constructor, then apply the recovery
theorem (or its `ProbComp` specialization) to interchange the two.
-/

open Interaction Interaction.UC

namespace Examples.UC.SyncRecoveryDemo

/-! ## Concrete closed-Party setup -/

/-- A single-party identity scheme: the demo only needs one party. -/
abbrev Party : Type := Unit

/-- The canonical scheduler sampler used throughout this demo: the trivial
`ProbComp` computation returning `ULift.up true`. Any concrete choice would do;
this one is the simplest. -/
def trivialSchedulerSampler : ProbComp (ULift Bool) :=
  pure (ULift.up true)

/-- The trivial closed process: single party, no boundary, `PUnit` state,
every step `.done`. This is the smallest object in the closed-Party
theory of `openTheory`. -/
def trivialClosed :
    (openTheory.{0, 0, 0, 0} Party ProbComp trivialSchedulerSampler).Closed :=
  openTheory_unit Party ProbComp

/-! ## Sync recovery at the `Semantics` level -/

/-- For any concrete sync `ProbComp` protocol, the trivial-env-scheduler
async lift built from `processSemanticsAsyncProbComp` agrees with the
synchronous `processSemanticsProbComp`.

This is just a typed restatement of
`processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial` at
`Party := Unit`; it confirms that the recovery theorem applies to a
fully concrete closed-Party identity scheme without any unfolding
boilerplate at the call site. -/
example
    (init : ∀ p :
      (openTheory.{0, 0, 0, 0} Party ProbComp trivialSchedulerSampler).Closed,
      p.Proc)
    (fuel : ℕ)
    (observe : ∀ p :
      (openTheory.{0, 0, 0, 0} Party ProbComp trivialSchedulerSampler).Closed,
      p.Proc → ProbComp Unit) :
    processSemanticsProbComp Party trivialSchedulerSampler
        init fuel observe =
      processSemanticsAsyncProbComp Party trivialSchedulerSampler
        (EnvAction.empty Unit) ()
        init
        (fun p => trivialEnvScheduler (m := ProbComp)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s) :=
  processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial
    Party trivialSchedulerSampler init fuel observe

/-! ## Sync recovery pointwise on the trivial closed process -/

/-- Specializing the recovery theorem to the trivial closed process and
unfolding both runtimes yields equality of the resulting `ProbComp Unit`
distributions, demonstrating that the synchronous and trivial-async
runtimes produce *the same* observable computation on a concrete
closed-Party value.

Proven by `Semantics.run`-level unfolding followed by
`Concurrent.runStepsAsync_empty_trivial_eq`. This mirrors the proof of
`processSemantics_eq_processSemanticsAsync_trivial` but avoids the
Semantics-level rewrite, which would have to transport through the
dependent surface-monad field `Semantics.m`. -/
example
    (init : ∀ p :
      (openTheory.{0, 0, 0, 0} Party ProbComp trivialSchedulerSampler).Closed,
      p.Proc)
    (fuel : ℕ)
    (observe : ∀ p :
      (openTheory.{0, 0, 0, 0} Party ProbComp trivialSchedulerSampler).Closed,
      p.Proc → ProbComp Unit) :
    (processSemanticsProbComp Party trivialSchedulerSampler
        init fuel observe).run trivialClosed =
      (processSemanticsAsyncProbComp Party trivialSchedulerSampler
        (EnvAction.empty Unit) ()
        init
        (fun p => trivialEnvScheduler (m := ProbComp)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s)).run trivialClosed := by
  change (do
      let finalState ← Concurrent.ProcessOver.runSteps
        trivialClosed.toProcess trivialClosed.stepSampler fuel
        (init trivialClosed)
      observe trivialClosed finalState) =
    (do
      let (final, _trace) ← Concurrent.runStepsAsync (m := ProbComp)
        trivialClosed.toProcess (EnvAction.empty Unit)
        (fun st => trivialClosed.stepSampler st.proc)
        (trivialEnvScheduler (m := ProbComp) Unit Empty)
        fuel ⟨init trivialClosed, ()⟩
      observe trivialClosed final.proc)
  rw [Concurrent.runStepsAsync_empty_trivial_eq]
  simp only [bind_assoc, pure_bind]

end Examples.UC.SyncRecoveryDemo

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

/-- The trivial closed process: single party, no boundary, `PUnit` state,
every step `.done`. This is the smallest object in the closed-Party
theory of `openTheory`. -/
def trivialClosed : (openTheory.{0, 0, 0} Party).Closed :=
  openTheory_unit Party

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
    (init : ∀ p : (openTheory.{0, 0, 0} Party).Closed, p.Proc)
    (sampler : ∀ (p : (openTheory.{0, 0, 0} Party).Closed) (s : p.Proc),
      Spec.Sampler ProbComp (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ p : (openTheory.{0, 0, 0} Party).Closed,
      p.Proc → ProbComp Unit) :
    processSemanticsProbComp Party init sampler fuel observe =
      processSemanticsAsyncProbComp Party
        (EnvAction.empty Unit) ()
        init
        (fun p st => sampler p st.proc)
        (fun p => trivialEnvScheduler (m := ProbComp)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s) :=
  processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial
    Party init sampler fuel observe

/-! ## Sync recovery pointwise on the trivial closed process -/

/-- Specializing the recovery theorem to the trivial closed process and
applying it on the `Semantics.run` field yields equality of the
resulting `ProbComp Unit` distributions, demonstrating that the
synchronous and trivial-async runtimes produce *the same* observable
computation on a concrete closed-Party value. -/
example
    (init : ∀ p : (openTheory.{0, 0, 0} Party).Closed, p.Proc)
    (sampler : ∀ (p : (openTheory.{0, 0, 0} Party).Closed) (s : p.Proc),
      Spec.Sampler ProbComp (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ p : (openTheory.{0, 0, 0} Party).Closed,
      p.Proc → ProbComp Unit) :
    (processSemanticsProbComp Party init sampler fuel observe).run
        trivialClosed =
      (processSemanticsAsyncProbComp Party
        (EnvAction.empty Unit) ()
        init
        (fun p st => sampler p st.proc)
        (fun p => trivialEnvScheduler (m := ProbComp)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s)).run trivialClosed := by
  rw [processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial]

end Examples.UC.SyncRecoveryDemo

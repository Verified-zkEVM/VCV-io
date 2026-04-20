/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.EnvOpenProcess
import VCVio.Interaction.UC.Runtime

/-!
# Asynchronous runtime semantics for env-open processes

This file defines the asynchronous-execution layer of the UC framework.
The runtime alternates between **process steps** (`processTick`) and
**environment-driven events** (`envTick e`) according to a pair of
schedulers; the alphabet of env events is supplied by an
`EnvAction Event State` (see `EnvAction.lean`).

The shape of every definition mirrors the synchronous `processSemantics`
in `Runtime.lean`: the bundled `SPMFSemantics m` is threaded uniformly,
so the same constructor serves coin-flip-only protocols, shared-oracle
protocols, and observation-style semantics that introduce failure mass.
The synchronous runtime is the special case in which the env scheduler
always returns `processTick` and the env alphabet is empty;
`processSemantics_eq_processSemanticsAsync_trivial` records that
equivalence by name, with `processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial`
giving the `ProbComp`-specialized form most coin-flip-only protocol
developments will reach for.

## Main definitions

* `RuntimeEvent Event` / `RuntimeTrace Event` — the observable trace
  alphabet, a sum of `processTick` and `envTick e`.
* `AsyncRuntimeState Proc State` — the joint state threaded through
  async execution: the residual process state plus the env-action
  bookkeeping state.
* `ProcessScheduler` / `EnvScheduler` — the two sibling samplers
  driving the async runtime. The process scheduler reuses the existing
  `Spec.Sampler m` from `Runtime.lean`; the env scheduler is a separate
  monadic choice over `RuntimeEvent`.
* `Concurrent.runStepsAsync` — the recursive engine. Mirrors
  `Concurrent.ProcessOver.runSteps` from `Runtime.lean`, with explicit
  env-event interleaving.
* `UC.processSemanticsAsync` — the headline `Semantics` constructor.
* `UC.processSemanticsAsyncProbComp` — the coin-flip-only specialization,
  companion to `processSemanticsProbComp`.
* `trivialEnvScheduler` — the env scheduler that always returns
  `processTick`.

## Universe constraints

The runtime layer requires move types, state types, **and the env-event
alphabet** to live at universe `0`, so that `ProbComp` and the runtime
monad `m : Type → Type` fit. This is strictly stronger than the data
layer in `EnvAction.lean` (which is generic in `Event : Type uE`)
because the runtime needs `m (RuntimeEvent Event)` to typecheck, and
`m : Type → Type` forces `RuntimeEvent Event : Type` and hence
`Event : Type`. Concrete env-event alphabets such as
`MomentaryCorruption.Alphabet Sid Pid` (with `Sid Pid : Type`) live at
universe `0`, so this is not a restriction in practice. The same
universe-`0` constraint applies to `processSemantics`.
-/

universe u

open OracleComp

namespace Interaction
namespace UC

/-! ## Runtime trace alphabet -/

/--
One tick of the async runtime: either a process step (no payload, the
actual move is sampled inside the `Spec`-driven `procScheduler`) or an
environment event carrying its alphabet symbol.

The sum is *non-symmetric* on purpose: `processTick` carries no payload
because the move space at a process step is determined by the process's
`Spec`, not by the runtime trace; `envTick` carries the alphabet symbol
because the `EnvAction.react` reaction is keyed by the symbol.
-/
inductive RuntimeEvent (Event : Type) where
  | processTick : RuntimeEvent Event
  | envTick (e : Event) : RuntimeEvent Event
  deriving DecidableEq

namespace RuntimeEvent

variable {Event : Type}

@[simp]
theorem processTick_ne_envTick (e : Event) :
    (processTick : RuntimeEvent Event) ≠ envTick e := by
  intro h; cases h

@[simp]
theorem envTick_ne_processTick (e : Event) :
    envTick e ≠ (processTick : RuntimeEvent Event) := by
  intro h; cases h

end RuntimeEvent

/--
The complete observable trace of one async run.

Async-runtime distributional reasoning compares distributions over
`RuntimeTrace × Result`, so this is the type forwarding and healing
lemmas work over.
-/
abbrev RuntimeTrace (Event : Type) : Type :=
  List (RuntimeEvent Event)

/-! ## Joint runtime state -/

/--
Joint state threaded through async execution: the residual process state
plus the env-action's bookkeeping state.

The runtime treats this structure opaquely through the `ProcessScheduler`
and `EnvScheduler` signatures, so a future reactive variant that adds
per-port pending packet queues (and possibly a queue of pending env
events) can extend this structure without invalidating the scheduler
APIs.
-/
@[ext]
structure AsyncRuntimeState (Proc : Type) (State : Type) where
  /-- The residual process state. -/
  proc : Proc
  /-- The env-action bookkeeping state. -/
  envState : State

namespace AsyncRuntimeState

variable {Proc State : Type}

@[simp]
theorem mk_eta (st : AsyncRuntimeState Proc State) :
    (⟨st.proc, st.envState⟩ : AsyncRuntimeState Proc State) = st := by
  cases st; rfl

end AsyncRuntimeState

/-! ## Schedulers -/

/--
A process scheduler picks a process-side `Spec.Sampler` at each step,
parameterized by the joint async-runtime state.

The sampler-side type `Spec.Sampler m (specOf st)` is the existing one
from `Runtime.lean`, unchanged. The extra `AsyncRuntimeState`-dependent
argument lets a scheduler refuse to schedule, e.g., a corrupted
machine's tick.
-/
abbrev ProcessScheduler
    (m : Type → Type) (Proc : Type) (State : Type)
    (specOf : AsyncRuntimeState Proc State → Spec.{0}) : Type :=
  ∀ st : AsyncRuntimeState Proc State, Spec.Sampler m (specOf st)

/--
An env scheduler chooses the next runtime event in the monad `m`.

Returning `processTick` yields control back to the process layer;
returning `envTick e` fires `e` against the env-action. This is the
sibling channel to `ProcessScheduler`: security definitions over the
async runtime quantify over both schedulers, so that the typed split
between adversary-controlled process scheduling and
environment-controlled env scheduling is preserved.
-/
abbrev EnvScheduler
    (m : Type → Type) (Proc : Type) (State : Type) (Event : Type) : Type :=
  AsyncRuntimeState Proc State → m (RuntimeEvent Event)

/--
The trivial env scheduler that always returns `processTick`.

Instantiating `processSemanticsAsync` at this scheduler with the empty
env alphabet recovers the synchronous `processSemantics`; see
`processSemantics_eq_processSemanticsAsync_trivial`.
-/
def trivialEnvScheduler {m : Type → Type} [Pure m]
    {Proc : Type} (State : Type) (Event : Type) :
    EnvScheduler m Proc State Event :=
  fun _ => pure RuntimeEvent.processTick

@[simp]
theorem trivialEnvScheduler_apply
    {m : Type → Type} [Pure m] {Proc State : Type} {Event : Type}
    (st : AsyncRuntimeState Proc State) :
    trivialEnvScheduler (m := m) State Event st =
      (pure RuntimeEvent.processTick : m (RuntimeEvent Event)) := rfl

end UC

/-! ## Async core engine -/

namespace Concurrent

open Interaction.UC

/--
Async core engine. Iterates `fuel` ticks, alternating between process
samples and env reactions according to `envScheduler`. Returns the
final joint state and the observable runtime trace.

Mirrors the recursion shape of `Concurrent.ProcessOver.runSteps` with
explicit env-event interleaving. The env reaction lives in `ProbComp`
(`EnvAction.react : Event → State → ProbComp State`) and is lifted into
the runtime monad `m` via `MonadLiftT ProbComp m`. The process sampler
type is unchanged from the synchronous runtime: the
`ProcessScheduler` carries the existing `Spec.Sampler m` from
`Runtime.lean`.
-/
noncomputable def runStepsAsync
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    {Γ : Spec.Node.Context}
    {State : Type} {Event : Type}
    (process : ProcessOver Γ)
    (envAction : Interaction.UC.EnvAction Event State)
    (procScheduler :
      Interaction.UC.ProcessScheduler m process.Proc State
        (fun st => (process.step st.proc).spec))
    (envScheduler :
      Interaction.UC.EnvScheduler m process.Proc State Event) :
    ℕ → AsyncRuntimeState process.Proc State →
      m (AsyncRuntimeState process.Proc State × RuntimeTrace Event)
  | 0,     st => pure (st, [])
  | n + 1, st => do
      let event ← envScheduler st
      let st' ← (match event with
        | .processTick => do
            let s' ← (process.step st.proc).sample (procScheduler st)
            pure ({ st with proc := s' } :
              AsyncRuntimeState process.Proc State)
        | .envTick e => do
            let es' ← (envAction.react e st.envState : ProbComp State)
            pure ({ st with envState := es' } :
              AsyncRuntimeState process.Proc State)
        : m (AsyncRuntimeState process.Proc State))
      let (final, tail) ← runStepsAsync process envAction
        procScheduler envScheduler n st'
      pure (final, event :: tail)

/--
Under the empty env alphabet (`EnvAction.empty Unit`) and the trivial env
scheduler (always `processTick`), `runStepsAsync` reduces to
`ProcessOver.runSteps` with the env state pinned to `()` and a constant
`processTick` trace.

This is the operational core of the sync-recovery story: it factors the
async engine into the synchronous `ProcessOver.runSteps` plus a trivial
trace bookkeeping pass, and is reused by
`UC.processSemantics_eq_processSemanticsAsync_trivial`.
-/
theorem runStepsAsync_empty_trivial_eq
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]
    {Γ : Spec.Node.Context}
    (process : ProcessOver Γ)
    (sampler : (s : process.Proc) → Spec.Sampler m (process.step s).spec)
    (fuel : ℕ) (s : process.Proc) :
    runStepsAsync (m := m) process (Interaction.UC.EnvAction.empty Unit)
        (fun st => sampler st.proc)
        (Interaction.UC.trivialEnvScheduler (m := m) Unit Empty)
        fuel
        (⟨s, ()⟩ : Interaction.UC.AsyncRuntimeState process.Proc Unit) =
      (do
        let s' ← ProcessOver.runSteps process sampler fuel s
        pure
          ((⟨s', ()⟩ : Interaction.UC.AsyncRuntimeState process.Proc Unit),
            List.replicate fuel Interaction.UC.RuntimeEvent.processTick)) := by
  induction fuel generalizing s with
  | zero =>
      simp [runStepsAsync, ProcessOver.runSteps]
  | succ n ih =>
      rw [runStepsAsync, ProcessOver.runSteps]
      simp only [Interaction.UC.trivialEnvScheduler_apply, pure_bind,
        bind_assoc, ih]
      rfl

end Concurrent

namespace UC

open Concurrent

private abbrev Closed (Party : Type u) (m : Type → Type)
    (schedulerSampler : m (ULift Bool)) :=
  (openTheory.{u, 0, 0, 0} Party m schedulerSampler).Closed

/--
Construct an async `Semantics` for the open-process theory.

Threads an env-action channel and an env scheduler in addition to the
process sampler that `processSemantics` already takes. The bundled
`SPMFSemantics m` plays the same role as in `processSemantics` and
supports the same instantiations: coin-flip-only protocols via
`processSemanticsAsyncProbComp`, shared-oracle protocols via an
`OracleComp`-monad `SPMFSemantics` built with `simulateQ'`, and
observation-style semantics over `OptionT ProbComp`.

The `init`, `procScheduler`, and `envScheduler` arguments are
quantified over the closed process `p : Closed Party`, matching the
shape of the synchronous `processSemantics`.
-/
noncomputable def processSemanticsAsync
    (Party : Type u)
    {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
    (schedulerSampler : m (ULift Bool))
    (sem : SPMFSemantics.{0, 0, 0} m)
    {Event : Type} {State : Type}
    (envAction : EnvAction Event State)
    (initEnvState : State)
    (init : ∀ p : Closed Party m schedulerSampler, p.Proc)
    (procScheduler : ∀ p : Closed Party m schedulerSampler,
      ProcessScheduler m p.Proc State
        (fun st => (p.step st.proc).spec))
    (envScheduler : ∀ p : Closed Party m schedulerSampler,
      EnvScheduler m p.Proc State Event)
    (fuel : ℕ)
    (observe : ∀ p : Closed Party m schedulerSampler,
      p.Proc → State → RuntimeTrace Event → m Unit) :
    Semantics (openTheory.{u, 0, 0, 0} Party m schedulerSampler) where
  m := m
  instMonad := inferInstance
  sem := sem
  run process := do
    let init0 : AsyncRuntimeState process.Proc State :=
      ⟨init process, initEnvState⟩
    let (final, trace) ← runStepsAsync process.toProcess envAction
      (procScheduler process) (envScheduler process) fuel init0
    observe process final.proc final.envState trace

/--
Coin-flip-only specialization of `processSemanticsAsync` (`m = ProbComp`,
`sem := SPMFSemantics.ofHasEvalSPMF ProbComp`). Companion of
`processSemanticsProbComp`.
-/
noncomputable def processSemanticsAsyncProbComp
    (Party : Type u)
    (schedulerSampler : ProbComp (ULift Bool))
    {Event : Type} {State : Type}
    (envAction : EnvAction Event State)
    (initEnvState : State)
    (init : ∀ p : Closed Party ProbComp schedulerSampler, p.Proc)
    (procScheduler : ∀ p : Closed Party ProbComp schedulerSampler,
      ProcessScheduler ProbComp p.Proc State
        (fun st => (p.step st.proc).spec))
    (envScheduler : ∀ p : Closed Party ProbComp schedulerSampler,
      EnvScheduler ProbComp p.Proc State Event)
    (fuel : ℕ)
    (observe : ∀ p : Closed Party ProbComp schedulerSampler,
      p.Proc → State → RuntimeTrace Event → ProbComp Unit) :
    Semantics (openTheory.{u, 0, 0, 0} Party ProbComp schedulerSampler) :=
  processSemanticsAsync Party schedulerSampler
    (SPMFSemantics.ofHasEvalSPMF ProbComp)
    envAction initEnvState
    init procScheduler envScheduler fuel observe

/-! ## Sync recovery -/

/--
The synchronous `processSemantics` is the special case of
`processSemanticsAsync` instantiated at:

* the empty env alphabet (`EnvAction.empty Unit`, with state `Unit`);
* the trivial env scheduler (always returns `processTick`);
* an `observe` that ignores the env state and the trace.

The proof factors through `Concurrent.runStepsAsync_empty_trivial_eq`,
which collapses the async engine to `ProcessOver.runSteps` together with
a constant `processTick` trace; the observe-side argument then drops the
trace and the unit env state.
-/
theorem processSemantics_eq_processSemanticsAsync_trivial
    (Party : Type u)
    {m : Type → Type} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]
    (schedulerSampler : m (ULift Bool))
    (sem : SPMFSemantics.{0, 0, 0} m)
    (init : ∀ p : Closed Party m schedulerSampler, p.Proc)
    (sampler : ∀ (p : Closed Party m schedulerSampler) (s : p.Proc),
      Spec.Sampler m (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ p : Closed Party m schedulerSampler, p.Proc → m Unit) :
    processSemantics Party schedulerSampler sem init sampler fuel observe =
      processSemanticsAsync Party schedulerSampler sem
        (EnvAction.empty Unit) ()
        init
        (fun p st => sampler p st.proc)
        (fun p => trivialEnvScheduler (m := m)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s) := by
  unfold processSemantics processSemanticsAsync
  congr 1
  funext process
  change (do
      let finalState ← ProcessOver.runSteps process.toProcess (sampler process)
        fuel (init process)
      observe process finalState) =
    (do
      let (final, _trace) ← Concurrent.runStepsAsync (m := m) process.toProcess
        (EnvAction.empty Unit)
        (fun st => sampler process st.proc)
        (trivialEnvScheduler (m := m) Unit Empty)
        fuel ⟨init process, ()⟩
      observe process final.proc)
  rw [Concurrent.runStepsAsync_empty_trivial_eq]
  simp only [bind_assoc, pure_bind]

/--
The `ProbComp` specialization of `processSemantics_eq_processSemanticsAsync_trivial`:
the synchronous `processSemanticsProbComp` equals the trivial async lift built
from `processSemanticsAsyncProbComp` with the empty env alphabet, the trivial
env scheduler, and an `observe` that ignores the env state and the trace.

This is the form most coin-flip-only protocol developments will reach for: it
discharges the `m`/`close`/`MonadLiftT` choices the general theorem leaves
abstract, leaving only the protocol-specific data (`init`, `sampler`, `fuel`,
`observe`) on each side of the equation.
-/
theorem processSemanticsProbComp_eq_processSemanticsAsyncProbComp_trivial
    (Party : Type u)
    (schedulerSampler : ProbComp (ULift Bool))
    (init : ∀ p : Closed Party ProbComp schedulerSampler, p.Proc)
    (sampler : ∀ (p : Closed Party ProbComp schedulerSampler) (s : p.Proc),
      Spec.Sampler ProbComp (p.step s).spec)
    (fuel : ℕ)
    (observe : ∀ p : Closed Party ProbComp schedulerSampler,
      p.Proc → ProbComp Unit) :
    processSemanticsProbComp Party schedulerSampler
        init sampler fuel observe =
      processSemanticsAsyncProbComp Party schedulerSampler
        (EnvAction.empty Unit) ()
        init
        (fun p st => sampler p st.proc)
        (fun p => trivialEnvScheduler (m := ProbComp)
          (Proc := p.Proc) Unit Empty)
        fuel
        (fun p s _ _ => observe p s) := by
  unfold processSemanticsProbComp processSemanticsAsyncProbComp
  exact processSemantics_eq_processSemanticsAsync_trivial _ _ _ _ _ _ _

end UC
end Interaction

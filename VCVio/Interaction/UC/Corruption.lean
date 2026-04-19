/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.EnvAction
import VCVio.Interaction.UC.EnvOpenProcess
import VCVio.Interaction.UC.MachineId
import VCVio.Interaction.Concurrent.Policy

/-!
# Adaptive momentary corruption vocabulary

This file introduces the standalone vocabulary for CJSV22-style adaptive
momentary corruption (Canetti, Jain, Swanberg, Varia, *Universally
Composable End-to-End Secure Messaging*, CRYPTO 2022 §3.2):

* **`CorruptionAlphabet Sid Pid`** — the inductive event alphabet
  `compromise(m)` and `refresh(m)`, indexed by `MachineId Sid Pid`.
* **`Epoch`** — the per-machine refresh counter, defined as `ℕ` (the
  simplest concrete choice; richer protocols like asymmetric ratchets
  can wrap this in their own `Epoch`-isomorphic type).
* **`CorruptionState Sid Pid`** — the two-flag corruption tracking:
  `corrupted` (current snapshot in adversary view) and `compromised`
  (per-`(machine, epoch)` historical view), plus the per-machine
  `epoch` counter.
* **`CorruptionState.applyCompromise` / `applyRefresh`** — the
  canonical deterministic updates triggered by the alphabet events.
* **`CorruptionState.envActionBase`** — the canonical `EnvAction`
  built from those updates, the baseline that every protocol opting
  in to adaptive momentary corruption inherits.
* **`LeakableState`** — the typeclass that surfaces the equivocability
  obligation as a missing instance. Real protocols supply the natural
  state projection; simulators supply a fabrication that is
  consistent with all prior leakages and the current trace.
* **`CorruptionPolicy`** — a `StepPolicy` specialization keyed on the
  corruption alphabet, reusing the existing `inter` / `top` /
  `byController` combinators from `Interaction.Concurrent.Policy`.
* **`CorruptionProcess Sid Pid Δ`** — the canonical instantiation of
  the generic `EnvOpenProcess` wrapper to the CJSV22 corruption
  alphabet and state.
* **`MachineProcess.withCorruption`** — the standard wrap that pairs a
  `MachineProcess` with `envActionBase` to produce a
  `CorruptionProcess`.

## Universe constraint

`Sid` and `Pid` live in `Type` (i.e. `Type 0`) because
`CorruptionState` participates in `ProbComp`-valued reactions and
`ProbComp : Type → Type`. This matches the universe convention used
in `VCVio/Interaction/UC/Runtime.lean`. Concrete protocol identity
types (`ℕ`, `String`, etc.) all satisfy this bound.

## Additive design

Like `EnvAction`, `CorruptionState` is **standalone**: it is *not*
threaded into `OpenNodeSemantics` here. Existing `OpenProcess`
constructions are untouched. The corruption-aware composition wrapper
`CorruptionProcess` (defined at the bottom of this file) is the
canonical inhabitant of the generic
`Interaction.UC.EnvOpenProcess Party Δ Event State` paired with the
corruption alphabet and state.

The four `*.corrupt` forwarding lemmas (CJSV22 §4.2) for `par` /
`wire` / `plug` are deferred to a follow-up slice: they require an
explicit choice of *combination strategy* (broadcast vs targeted vs
Kleisli-sequential) on the env channel of composites, and the
targeted-routing variant also needs `HasAccessControl` integration
which is currently still declarative. See the F2 design memo for the
full roadmap.

## Why `LeakableState` is a typeclass

Forcing every protocol that participates in adaptive corruption to
declare what it leaks turns the equivocability obligation into a
mechanically checkable instance hole. A simulator that cannot
fabricate consistent state cannot supply an instance and cannot be
plugged into the security definition; the obligation is enforced at
compile time rather than via meta-theoretic side conditions.

## Decidability

All comparisons are over `MachineId` (which derives `DecidableEq`
from `[DecidableEq Sid] [DecidableEq Pid]`) and over `Epoch = ℕ`.
`CorruptionState` operations are computable as long as the user
provides decidable equality on the identity type parameters.
-/

universe v w w₂

namespace Interaction
namespace UC

/-! ## Corruption alphabet and epoch -/

/--
The standard CJSV22 corruption alphabet for a fixed `(Sid, Pid)`
identity space.

* `compromise m` snapshots the current state of machine `m` into the
  adversary's view: the leakage function fires, and the current epoch
  of `m` is marked compromised.
* `refresh m` advances the epoch counter for `m`. After a refresh,
  future epochs of `m` are not (yet) compromised; the protocol's
  forward-secrecy mechanism gets a chance to heal.

The pair `(compromise, refresh)` is the alphabet underlying the
*momentary* part of "adaptive momentary corruption": at any point the
environment may compromise a machine, and a subsequent refresh
recovers post-compromise security for future epochs.

`CorruptionAlphabet Sid Pid` is the canonical instantiation of
`EnvAction.alphabet` for adaptive momentary corruption. The
`EnvAction` paired with this alphabet is built from
`CorruptionState.envActionBase`.
-/
inductive CorruptionAlphabet (Sid Pid : Type) where
  /-- Snapshot the current state of `m` into the adversary's view. -/
  | compromise (m : MachineId Sid Pid) : CorruptionAlphabet Sid Pid
  /-- Advance the epoch counter of `m`, enabling forward healing. -/
  | refresh    (m : MachineId Sid Pid) : CorruptionAlphabet Sid Pid
deriving DecidableEq

namespace CorruptionAlphabet

variable {Sid Pid : Type}

/-- The machine targeted by a corruption event. -/
def target : CorruptionAlphabet Sid Pid → MachineId Sid Pid
  | .compromise m => m
  | .refresh m    => m

@[simp] theorem target_compromise (m : MachineId Sid Pid) :
    (compromise m).target = m := rfl

@[simp] theorem target_refresh (m : MachineId Sid Pid) :
    (refresh m).target = m := rfl

end CorruptionAlphabet

/--
`Epoch` indexes the per-machine refresh cycles.

A flat `ℕ` is the simplest concrete choice: refresh counts as
`epoch m += 1`. Richer protocols (e.g. Signal's asymmetric ratchet
with separate sending and receiving counters) can wrap this in their
own `Epoch`-isomorphic type; the framework only requires
`DecidableEq` and a way to advance.
-/
abbrev Epoch : Type := ℕ

/-! ## Corruption state -/

/--
`CorruptionState Sid Pid` packages the two-flag corruption tracking
that an environment-driven step carries between events.

* `corrupted m = true` iff the current state of `m` has been
  snapshotted by the adversary at least once and not refreshed
  since. Mutated by `compromise m` (sets `true`) and `refresh m`
  (sets `false`).
* `compromised m e = true` iff the secrets for epoch `e` of `m`
  are in the adversary's view. Strictly accumulating: a compromise
  event sets `compromised m (current_epoch m)`; epochs once
  compromised stay compromised forever.
* `epoch m` is `m`'s current refresh counter. Mutated by
  `refresh m` (increments by one).

The two flags `corrupted` and `compromised` are deliberately
independent:

* `corrupted m` may be `false` while `compromised m e` holds for
  some past `e`: the adversary saw that epoch's secret, but the
  machine has since refreshed and now has a fresh secret.
* `corrupted m` may be `true` while `compromised m e'` is `false`
  for some future `e'`: a forward-secret key schedule may
  forward-decrypt only a bounded window from a current compromise.

Two flags, two distinct purposes. The naming deliberately avoids
the ambiguous "exposed", which would collide with `OpenTheory`'s
boundary-exposure terminology.
-/
@[ext]
structure CorruptionState (Sid Pid : Type) where
  /-- Per-machine snapshot flag, mutated by `compromise` and `refresh`. -/
  corrupted : MachineId Sid Pid → Bool := fun _ => false
  /-- Per-(machine, epoch) leak flag, monotonically accumulating. -/
  compromised : MachineId Sid Pid → Epoch → Bool := fun _ _ => false
  /-- Per-machine refresh counter, advanced by `refresh`. -/
  epoch : MachineId Sid Pid → Epoch := fun _ => 0

namespace CorruptionState

variable {Sid Pid : Type}

/-- The fully-honest initial state: nothing corrupted, nothing
compromised, every machine at epoch zero. -/
def init : CorruptionState Sid Pid := {}

instance : Inhabited (CorruptionState Sid Pid) := ⟨init⟩

@[simp] theorem corrupted_init (m : MachineId Sid Pid) :
    (init : CorruptionState Sid Pid).corrupted m = false := rfl

@[simp] theorem compromised_init (m : MachineId Sid Pid) (e : Epoch) :
    (init : CorruptionState Sid Pid).compromised m e = false := rfl

@[simp] theorem epoch_init (m : MachineId Sid Pid) :
    (init : CorruptionState Sid Pid).epoch m = 0 := rfl

variable [DecidableEq Sid] [DecidableEq Pid]

/--
Apply `compromise m` to the corruption state: set `corrupted m` and
mark the current epoch of `m` as compromised. The epoch counter is
not advanced.

This is a deterministic update, so the value lives in the underlying
`CorruptionState`; the canonical `EnvAction` reaction wraps it via
`pure`.
-/
def applyCompromise
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    CorruptionState Sid Pid where
  corrupted := Function.update cs.corrupted m true
  compromised := fun m' e' =>
    cs.compromised m' e' || (decide (m = m') && decide (e' = cs.epoch m))
  epoch := cs.epoch

/--
Apply `refresh m` to the corruption state: clear `corrupted m` and
advance the epoch counter of `m` by one. Past `compromised` flags are
preserved (they are historical and accumulate).

After a refresh, future events on `m` write into the new epoch; this
is the structural ingredient that lets the framework derive PCS
(post-compromise security) as a healing theorem rather than as an
axiom.
-/
def applyRefresh
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    CorruptionState Sid Pid where
  corrupted := Function.update cs.corrupted m false
  compromised := cs.compromised
  epoch := Function.update cs.epoch m (cs.epoch m + 1)

/--
The canonical `EnvAction` reaction for the corruption alphabet:
`compromise` snapshots, `refresh` advances the epoch.

This is the baseline used by every protocol that opts in to
adaptive momentary corruption. Protocols that need richer
per-event behaviour (e.g. simulator-controlled randomization on
`compromise`, or a non-trivial leakage function) override the
relevant branch in their bespoke `EnvAction` rather than touching
the alphabet itself.
-/
def reactBase
    (s : CorruptionAlphabet Sid Pid) (cs : CorruptionState Sid Pid) :
    ProbComp (CorruptionState Sid Pid) :=
  match s with
  | .compromise m => pure (applyCompromise m cs)
  | .refresh m    => pure (applyRefresh m cs)

/-- The canonical corruption-aware `EnvAction`. -/
def envActionBase :
    EnvAction (CorruptionAlphabet Sid Pid) (CorruptionState Sid Pid) where
  react := reactBase

@[simp] theorem reactBase_compromise
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    reactBase (.compromise m) cs = pure (applyCompromise m cs) := rfl

@[simp] theorem reactBase_refresh
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    reactBase (.refresh m) cs = pure (applyRefresh m cs) := rfl

@[simp] theorem corrupted_applyCompromise_self
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyCompromise m cs).corrupted m = true := by
  simp [applyCompromise]

theorem corrupted_applyCompromise_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : CorruptionState Sid Pid) :
    (applyCompromise m cs).corrupted m' = cs.corrupted m' := by
  simp [applyCompromise, Function.update_of_ne h]

@[simp] theorem corrupted_applyRefresh_self
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyRefresh m cs).corrupted m = false := by
  simp [applyRefresh]

theorem corrupted_applyRefresh_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : CorruptionState Sid Pid) :
    (applyRefresh m cs).corrupted m' = cs.corrupted m' := by
  simp [applyRefresh, Function.update_of_ne h]

@[simp] theorem epoch_applyCompromise
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyCompromise m cs).epoch = cs.epoch := rfl

@[simp] theorem epoch_applyRefresh_self
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyRefresh m cs).epoch m = cs.epoch m + 1 := by
  simp [applyRefresh]

theorem epoch_applyRefresh_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : CorruptionState Sid Pid) :
    (applyRefresh m cs).epoch m' = cs.epoch m' := by
  simp [applyRefresh, Function.update_of_ne h]

theorem compromised_applyCompromise_self_currentEpoch
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyCompromise m cs).compromised m (cs.epoch m) = true := by
  simp [applyCompromise]

/--
`compromise` is monotone: once an epoch is in the adversary's view, it
stays in the adversary's view. This is the structural fact that makes
PCS (post-compromise security) about *future* epochs rather than
about un-leaking past ones.
-/
theorem compromised_applyCompromise_of_compromised
    {cs : CorruptionState Sid Pid} {m : MachineId Sid Pid}
    {m' : MachineId Sid Pid} {e : Epoch}
    (h : cs.compromised m' e = true) :
    (applyCompromise m cs).compromised m' e = true := by
  simp [applyCompromise, h]

/-- `refresh` preserves all past compromise flags. -/
@[simp] theorem compromised_applyRefresh
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    (applyRefresh m cs).compromised = cs.compromised := rfl

end CorruptionState

/-! ## Leakable state (equivocability obligation) -/

/--
`LeakableState State Leakage` exposes an extraction function that
projects a per-machine snapshot from `State`.

The intended use is on `MachineProcess`-shaped state types: a real
protocol supplies the natural projection (e.g. "current long-term
secret + ratchet root for machine `m`"); a simulator supplies a
fabrication consistent with all prior leakages and the current
adversary trace.

This is the typed form of the **equivocability obligation** from
CJSV22 §4.1. By exposing it as a typeclass, the framework forces the
following invariant at compile time: a simulator that cannot
fabricate consistent state cannot supply an instance, and cannot be
used to discharge UC security. The obligation becomes a *missing
instance* error rather than a meta-theoretic gap in the proof.

`Leakage` is an `outParam` because each `State` functionally
determines its leakage type: there is one canonical projection per
protocol, and ambiguity should not arise during instance synthesis.

There is **no default instance**. Forcing every protocol to declare
what it leaks is intentional: an automatic default would either leak
too much (the entire `State`, breaking forward-secrecy proofs) or
too little (nothing, vacuously satisfying the typeclass).
-/
class LeakableState
    {Sid Pid : Type} (State : Type)
    (Leakage : outParam Type) where
  leak : State → MachineId Sid Pid → Leakage

/-! ## Corruption policy -/

open Interaction.Concurrent

/--
`CorruptionPolicy process` is a `StepPolicy` specialization that
constrains the environment's corruption capabilities at each
process step.

Concretely: a corruption policy is given the concrete step transcript
of a process and decides whether the step is admissible. Reuses the
existing `Concurrent.ProcessOver.StepPolicy` machinery
(`Interaction/Concurrent/Policy.lean`) verbatim, so the standard
`top` / `inter` / `byController` / `byPath` / `byEvent` / `byTicket`
combinators apply unchanged.

Common downstream policies (none specialized here yet — they live with
their pilot protocols):

* `static` — only allow `compromise` events before any `send`-class
  event has fired.
* `momentary` — allow at most one `compromise(m)` per epoch per
  machine (the CJSV22 default).
* `bounded n` — allow at most `n` compromises across the whole
  trace.

These are **policies on the underlying step transcripts**, not on the
corruption alphabet directly. The corruption alphabet flows through
the `EnvAction` channel of a corruption-aware process; the policy
constrains which step transcripts (which carry the env event in their
data) the environment is allowed to schedule.
-/
abbrev CorruptionPolicy
    {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver Γ) :=
  ProcessOver.StepPolicy process

namespace CorruptionPolicy

variable {Γ : Interaction.Spec.Node.Context.{w, w₂}} {process : ProcessOver Γ}

/-- Allow every step transcript: the unconstrained baseline. -/
abbrev top : CorruptionPolicy process :=
  ProcessOver.StepPolicy.top

/-- Conjunction of two corruption policies: both must allow. -/
abbrev inter (left right : CorruptionPolicy process) :
    CorruptionPolicy process :=
  ProcessOver.StepPolicy.inter left right

end CorruptionPolicy

/-! ## Canonical corruption-aware open process -/

/--
`CorruptionProcess Sid Pid Δ` is the canonical CJSV22-flavoured
instantiation of `EnvOpenProcess`: a `MachineProcess Sid Pid Δ` paired
with the corruption-event channel
`EnvAction (CorruptionAlphabet Sid Pid) (CorruptionState Sid Pid)`.

This is one consumer of the generic `EnvOpenProcess` wrapper. Other
environment-driven channels (broadcast resets, time advance,
simulator-controlled reseed, side-channel leakage) reuse the same
wrapper with different `(Event, State)` pairs; nothing in
`EnvOpenProcess` is corruption-specific. The wrapper-level genericity
lets us defer revisiting the (currently Signal-flavoured)
`CorruptionAlphabet` and `CorruptionState` themselves to a later
generalization pass without re-cutting the env-channel foundation.

The two `OpenProcess` universe parameters `v` (process state) and `w`
(move spaces) are exposed; the participant universe is fixed to `0`
because `MachineId Sid Pid : Type 0` (`Sid Pid : Type`).
-/
abbrev CorruptionProcess (Sid Pid : Type) (Δ : PortBoundary) :=
  EnvOpenProcess.{0, 0, v, w} (MachineId Sid Pid) Δ
    (CorruptionAlphabet Sid Pid) (CorruptionState Sid Pid)

/--
Wrap a `MachineProcess Sid Pid Δ` with the canonical CJSV22 corruption
env channel `envActionBase`, yielding a `CorruptionProcess`.

This is the **standard inhabitant** of `CorruptionProcess`:
`compromise(m)` snapshots `m`'s current epoch into the adversary's
view (sets `corrupted m` and `compromised m (epoch m)`), and
`refresh(m)` advances `m`'s epoch counter and clears `corrupted m`.

Protocols that need richer per-event behaviour (e.g.
simulator-controlled randomization on `compromise`, or a non-trivial
leakage function that depends on the protocol state) build their
`EnvOpenProcess` directly with a bespoke `EnvAction` rather than going
through `withCorruption`.
-/
def MachineProcess.withCorruption
    {Sid Pid : Type} {Δ : PortBoundary}
    [DecidableEq Sid] [DecidableEq Pid]
    (P : MachineProcess.{0, v, w} Sid Pid Δ) :
    CorruptionProcess.{v, w} Sid Pid Δ where
  process := P
  envAction := CorruptionState.envActionBase

namespace MachineProcess

variable {Sid Pid : Type} {Δ : PortBoundary}
  [DecidableEq Sid] [DecidableEq Pid]

@[simp]
theorem process_withCorruption (P : MachineProcess.{0, v, w} Sid Pid Δ) :
    P.withCorruption.process = P := rfl

@[simp]
theorem envAction_withCorruption (P : MachineProcess.{0, v, w} Sid Pid Δ) :
    P.withCorruption.envAction = CorruptionState.envActionBase := rfl

@[simp]
theorem react_withCorruption_compromise
    (P : MachineProcess.{0, v, w} Sid Pid Δ)
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    P.withCorruption.react (.compromise m) cs =
      pure (CorruptionState.applyCompromise m cs) := rfl

@[simp]
theorem react_withCorruption_refresh
    (P : MachineProcess.{0, v, w} Sid Pid Δ)
    (m : MachineId Sid Pid) (cs : CorruptionState Sid Pid) :
    P.withCorruption.react (.refresh m) cs =
      pure (CorruptionState.applyRefresh m cs) := rfl

end MachineProcess

end UC
end Interaction

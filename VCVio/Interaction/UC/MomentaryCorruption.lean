/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.UC.CorruptionModel
import VCVio.Interaction.UC.EnvAction
import VCVio.Interaction.UC.EnvOpenProcess
import VCVio.Interaction.UC.MachineId

/-!
# Momentary corruption: the CJSV22 corruption model

This file ships the **momentary corruption model**: the canonical
adaptive corruption model with refresh-based healing introduced in
Canetti, Jain, Swanberg, Varia, *Universally Composable End-to-End
Secure Messaging* (CRYPTO 2022, §3.2). All names live under the
`MomentaryCorruption.*` namespace so it is unambiguous which
*model* (in the sense of `CorruptionModel`) is in scope.

The model captures:

* **Adaptive compromise.** The environment may issue
  `compromise(m)` for any machine `m` at any time, marking `m`'s
  current epoch as compromised in the adversary's view.
* **Refresh-based healing.** A subsequent `refresh(m)` advances
  `m`'s epoch counter and clears the current `corrupted` snapshot
  flag; future epochs are not (yet) compromised. This is the
  structural ingredient that lets the framework derive
  post-compromise security as a healing theorem rather than as an
  axiom.

The bundled value `MomentaryCorruption.model Sid Pid` is a
`CorruptionModel` whose `Event` is `Alphabet Sid Pid` and whose
`State` is `State Sid Pid` (the two-flag plus epoch tracking).

## Contents

* **`Alphabet Sid Pid`** — inductive event alphabet
  `compromise(m) | refresh(m)`, indexed by `MachineId Sid Pid`.
* **`Epoch`** — the per-machine refresh counter (a `ℕ` abbrev).
* **`State Sid Pid`** — two-flag corruption tracking
  (`corrupted`, `compromised`) plus the per-machine `epoch`
  counter.
* **`State.applyCompromise` / `State.applyRefresh`** — the
  canonical deterministic updates triggered by alphabet events.
* **`react`** — the `Alphabet → State → ProbComp State` reaction
  driving the model's `EnvAction`.
* **`envAction`** — the canonical `EnvAction Alphabet State` for
  the model.
* **`model Sid Pid`** — the bundled `CorruptionModel` value.
* **`Process Sid Pid Δ`** — the corruption-aware open-process
  abbreviation: `EnvOpenProcess` of a `MachineProcess` with this
  model's env channel.
* **`MachineProcess.withMomentaryCorruption`** — the standard
  wrapping that turns a `MachineProcess` into a `Process`.

## Universe constraint

`Sid` and `Pid` live in `Type` (i.e. `Type 0`) because `State`
participates in `ProbComp`-valued reactions and
`ProbComp : Type → Type`. Concrete protocol identity types
(`ℕ`, `String`, etc.) all satisfy this bound. The two `OpenProcess`
universes `(v, w)` are exposed.

## Additive design

The model is **standalone**: nothing here is threaded into
`OpenNodeProfile`. Existing `OpenProcess` constructions are
untouched. The corruption-aware composition operators (par / wire /
plug lifted from `OpenTheory`) and the four `*.corrupt` forwarding
lemmas (CJSV22 §4.2) live in a downstream layer that consumes
`Process` and the model's bundled `envAction`; this file ships only
the data and the per-event reactions.

## Decidability

All comparisons are over `MachineId` (which derives `DecidableEq`
from `[DecidableEq Sid] [DecidableEq Pid]`) and over `Epoch = ℕ`.
The deterministic state updates require `[DecidableEq Sid]
[DecidableEq Pid]`; the alphabet, state, and process types
themselves do not.
-/

universe v w w'

namespace Interaction
namespace UC
namespace MomentaryCorruption

/-! ## Alphabet and epoch -/

/--
The momentary-corruption event alphabet.

* `compromise m` snapshots the current state of machine `m` into
  the adversary's view: a leakage observer (declared separately,
  e.g. via `SnapshotLeakable`) fires, and the current epoch of `m`
  is marked compromised in the bookkeeping state.
* `refresh m` advances the epoch counter for `m` and clears the
  current snapshot flag. After a refresh, future epochs of `m` are
  not (yet) compromised; the protocol's forward-secrecy mechanism
  gets a chance to heal.

The pair `(compromise, refresh)` is what makes corruption
*momentary* (rather than persistent): at any point the environment
may compromise a machine, and a subsequent refresh recovers
post-compromise security for future epochs.
-/
inductive Alphabet (Sid Pid : Type) where
  /-- Snapshot the current state of `m` into the adversary's view. -/
  | compromise (m : MachineId Sid Pid) : Alphabet Sid Pid
  /-- Advance the epoch counter of `m`, enabling forward healing. -/
  | refresh    (m : MachineId Sid Pid) : Alphabet Sid Pid
deriving DecidableEq

namespace Alphabet

variable {Sid Pid : Type}

/-- The machine targeted by an event. -/
def target : Alphabet Sid Pid → MachineId Sid Pid
  | .compromise m => m
  | .refresh m    => m

@[simp] theorem target_compromise (m : MachineId Sid Pid) :
    (compromise m).target = m := rfl

@[simp] theorem target_refresh (m : MachineId Sid Pid) :
    (refresh m).target = m := rfl

end Alphabet

/--
`Epoch` indexes the per-machine refresh cycles.

A flat `ℕ` is the simplest concrete choice: refresh counts as
`epoch m += 1`. Richer protocols (e.g. Signal's asymmetric ratchet
with separate sending and receiving counters) can wrap this in
their own `Epoch`-isomorphic type; the model only requires
`DecidableEq` and a way to advance.
-/
abbrev Epoch : Type := ℕ

/-! ## Bookkeeping state -/

/--
`State Sid Pid` packages the two-flag corruption tracking that the
model carries between events.

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
structure State (Sid Pid : Type) where
  /-- Per-machine snapshot flag, mutated by `compromise` and `refresh`. -/
  corrupted : MachineId Sid Pid → Bool := fun _ => false
  /-- Per-(machine, epoch) leak flag, monotonically accumulating. -/
  compromised : MachineId Sid Pid → Epoch → Bool := fun _ _ => false
  /-- Per-machine refresh counter, advanced by `refresh`. -/
  epoch : MachineId Sid Pid → Epoch := fun _ => 0

namespace State

variable {Sid Pid : Type}

/--
The fully-honest initial state: nothing corrupted, nothing
compromised, every machine at epoch zero.
-/
def init : State Sid Pid := {}

instance : Inhabited (State Sid Pid) := ⟨init⟩

@[simp] theorem corrupted_init (m : MachineId Sid Pid) :
    (init : State Sid Pid).corrupted m = false := rfl

@[simp] theorem compromised_init (m : MachineId Sid Pid) (e : Epoch) :
    (init : State Sid Pid).compromised m e = false := rfl

@[simp] theorem epoch_init (m : MachineId Sid Pid) :
    (init : State Sid Pid).epoch m = 0 := rfl

variable [DecidableEq Sid] [DecidableEq Pid]

/--
Apply `compromise m` to the bookkeeping state: set `corrupted m`
and mark the current epoch of `m` as compromised. The epoch counter
is not advanced.

This is a deterministic update, so the value lives in the
underlying `State`; the canonical `EnvAction` reaction wraps it
via `pure`.
-/
def applyCompromise
    (m : MachineId Sid Pid) (cs : State Sid Pid) : State Sid Pid where
  corrupted := Function.update cs.corrupted m true
  compromised := fun m' e' =>
    cs.compromised m' e' || (decide (m = m') && decide (e' = cs.epoch m))
  epoch := cs.epoch

/--
Apply `refresh m` to the bookkeeping state: clear `corrupted m`
and advance the epoch counter of `m` by one. Past `compromised`
flags are preserved (they are historical and accumulate).

After a refresh, future events on `m` write into the new epoch;
this is the structural ingredient that lets the model derive PCS
(post-compromise security) as a healing theorem rather than as an
axiom.
-/
def applyRefresh
    (m : MachineId Sid Pid) (cs : State Sid Pid) : State Sid Pid where
  corrupted := Function.update cs.corrupted m false
  compromised := cs.compromised
  epoch := Function.update cs.epoch m (cs.epoch m + 1)

@[simp] theorem corrupted_applyCompromise_self
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyCompromise m cs).corrupted m = true := by
  simp [applyCompromise]

theorem corrupted_applyCompromise_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : State Sid Pid) :
    (applyCompromise m cs).corrupted m' = cs.corrupted m' := by
  simp [applyCompromise, Function.update_of_ne h]

@[simp] theorem corrupted_applyRefresh_self
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyRefresh m cs).corrupted m = false := by
  simp [applyRefresh]

theorem corrupted_applyRefresh_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : State Sid Pid) :
    (applyRefresh m cs).corrupted m' = cs.corrupted m' := by
  simp [applyRefresh, Function.update_of_ne h]

@[simp] theorem epoch_applyCompromise
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyCompromise m cs).epoch = cs.epoch := rfl

@[simp] theorem epoch_applyRefresh_self
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyRefresh m cs).epoch m = cs.epoch m + 1 := by
  simp [applyRefresh]

theorem epoch_applyRefresh_of_ne
    {m m' : MachineId Sid Pid} (h : m' ≠ m) (cs : State Sid Pid) :
    (applyRefresh m cs).epoch m' = cs.epoch m' := by
  simp [applyRefresh, Function.update_of_ne h]

theorem compromised_applyCompromise_self_currentEpoch
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyCompromise m cs).compromised m (cs.epoch m) = true := by
  simp [applyCompromise]

/--
`compromise` is monotone: once an epoch is in the adversary's view,
it stays in the adversary's view. This is the structural fact that
makes PCS (post-compromise security) about *future* epochs rather
than about un-leaking past ones.
-/
theorem compromised_applyCompromise_of_compromised
    {cs : State Sid Pid} {m : MachineId Sid Pid}
    {m' : MachineId Sid Pid} {e : Epoch}
    (h : cs.compromised m' e = true) :
    (applyCompromise m cs).compromised m' e = true := by
  simp [applyCompromise, h]

/-- `refresh` preserves all past compromise flags. -/
@[simp] theorem compromised_applyRefresh
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    (applyRefresh m cs).compromised = cs.compromised := rfl

end State

/-! ## Reaction and bundled model -/

variable {Sid Pid : Type} [DecidableEq Sid] [DecidableEq Pid]

/--
The canonical `EnvAction` reaction for the momentary-corruption
alphabet: `compromise` snapshots, `refresh` advances the epoch.

This is the baseline used by every protocol that opts in to
momentary corruption. Protocols that need richer per-event
behaviour (e.g. simulator-controlled randomization on `compromise`,
or a non-trivial leakage function) build their own `EnvAction`
rather than overriding individual branches here.
-/
def react
    (s : Alphabet Sid Pid) (cs : State Sid Pid) :
    ProbComp (State Sid Pid) :=
  match s with
  | .compromise m => pure (State.applyCompromise m cs)
  | .refresh m    => pure (State.applyRefresh m cs)

/-- The canonical momentary-corruption `EnvAction`. -/
def envAction : EnvAction (Alphabet Sid Pid) (State Sid Pid) where
  react := react

@[simp] theorem react_compromise
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    react (.compromise m) cs = pure (State.applyCompromise m cs) := rfl

@[simp] theorem react_refresh
    (m : MachineId Sid Pid) (cs : State Sid Pid) :
    react (.refresh m) cs = pure (State.applyRefresh m cs) := rfl

@[simp] theorem envAction_react :
    (envAction (Sid := Sid) (Pid := Pid)).react = react := rfl

/--
The momentary-corruption model bundled as a `CorruptionModel`.

Use this when you want to talk about the model abstractly through
the `CorruptionModel` API — for instance, when stating a lemma
that is generic over corruption models but instantiated to the
momentary case at a use site.
-/
def model (Sid Pid : Type) [DecidableEq Sid] [DecidableEq Pid] :
    CorruptionModel where
  Event := Alphabet Sid Pid
  State := State Sid Pid
  envAction := envAction

@[simp] theorem model_Event :
    (model Sid Pid).Event = Alphabet Sid Pid := rfl

@[simp] theorem model_State :
    (model Sid Pid).State = State Sid Pid := rfl

@[simp] theorem model_envAction :
    (model Sid Pid).envAction = envAction := rfl

/-! ## Canonical corruption-aware open process -/

/--
`Process Sid Pid Δ` is the canonical open process for the
momentary-corruption model: a `MachineProcess Sid Pid Δ` paired
with this model's env channel.

Type-level definition does not depend on `[DecidableEq Sid]
[DecidableEq Pid]`; the typeclass requirements only appear when one
constructs the env action's reaction (e.g. via
`MachineProcess.withMomentaryCorruption`).
-/
abbrev Process (Sid Pid : Type) (m : Type w → Type w') (Δ : PortBoundary) :=
  EnvOpenProcess.{0, 0, v, w, w'} m (MachineId Sid Pid) Δ
    (Alphabet Sid Pid) (State Sid Pid)

end MomentaryCorruption

/--
Wrap a `MachineProcess Sid Pid Δ` with the canonical
momentary-corruption env channel, yielding a
`MomentaryCorruption.Process`.

This is the **standard inhabitant**: `compromise(m)` snapshots
`m`'s current epoch into the adversary's view (sets `corrupted m`
and `compromised m (epoch m)`), and `refresh(m)` advances `m`'s
epoch counter and clears `corrupted m`.

Protocols that need richer per-event behaviour (e.g.
simulator-controlled randomization on `compromise`, or a
non-trivial leakage function that depends on the protocol state)
build their `EnvOpenProcess` directly with a bespoke `EnvAction`
rather than going through this wrapping.
-/
def MachineProcess.withMomentaryCorruption
    {Sid Pid : Type} {m : Type w → Type w'} {Δ : PortBoundary}
    [DecidableEq Sid] [DecidableEq Pid]
    (P : MachineProcess.{0, v, w, w'} Sid Pid m Δ) :
    MomentaryCorruption.Process.{v, w, w'} Sid Pid m Δ where
  process := P
  envAction := MomentaryCorruption.envAction

namespace MachineProcess

variable {Sid Pid : Type} {m : Type w → Type w'} {Δ : PortBoundary}
  [DecidableEq Sid] [DecidableEq Pid]

@[simp]
theorem process_withMomentaryCorruption
    (P : MachineProcess.{0, v, w, w'} Sid Pid m Δ) :
    P.withMomentaryCorruption.process = P := rfl

@[simp]
theorem envAction_withMomentaryCorruption
    (P : MachineProcess.{0, v, w, w'} Sid Pid m Δ) :
    P.withMomentaryCorruption.envAction = MomentaryCorruption.envAction := rfl

@[simp]
theorem react_withMomentaryCorruption_compromise
    (P : MachineProcess.{0, v, w, w'} Sid Pid m Δ)
    (mid : MachineId Sid Pid) (cs : MomentaryCorruption.State Sid Pid) :
    P.withMomentaryCorruption.react (.compromise mid) cs =
      pure (MomentaryCorruption.State.applyCompromise mid cs) := rfl

@[simp]
theorem react_withMomentaryCorruption_refresh
    (P : MachineProcess.{0, v, w, w'} Sid Pid m Δ)
    (mid : MachineId Sid Pid) (cs : MomentaryCorruption.State Sid Pid) :
    P.withMomentaryCorruption.react (.refresh mid) cs =
      pure (MomentaryCorruption.State.applyRefresh mid cs) := rfl

end MachineProcess

end UC
end Interaction

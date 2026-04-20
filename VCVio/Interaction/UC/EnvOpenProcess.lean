/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.EnvAction

/-!
# Open processes paired with an environment-event channel

This file introduces `EnvOpenProcess Party Δ Event State`, the
structural pairing of an `OpenProcess Party Δ` (port-routed
boundary channel) with an `EnvAction Event State` (environment-fired
event channel). See `EnvAction.lean` for the motivation behind the
two-channel split (port traffic through `BoundaryAction`,
environment effects through `EnvAction`).

## What the wrapper adds beyond `OpenProcess + EnvAction`

The wrapper does two concrete jobs that an ad-hoc tuple does not:

1. **Bundling.** A "process that has an environment channel" is a
   *single value* you can pass around, return from a function, store
   in a structure. Without the wrapper, every consumer would have
   to re-tuple `(P : OpenProcess _ _, ea : EnvAction _ _)` at every
   call site. Composition operators, runtime scheduling, security
   games — they all need the pair to travel together.

2. **An opt-in surface.** Existing `OpenProcess` values are
   unchanged. A consumer that doesn't care about environment
   actions never imports this file. A consumer that does, gets the
   pair as a structure with a typed `react` projection. The env
   channel is **additive** above `OpenProcess` and never threaded
   into `OpenNodeProfile`, so adding it costs zero in the rest of
   the framework.

The alternative, threading the env-event alphabet `Σ` (with
`Σ := Empty` default) directly through `OpenNodeProfile`, would
touch every existing constructor and every `_iso` lemma in
`OpenProcessModel.lean`. The wrapper achieves the same expressive
power additively, with zero invasion.

## Genericity

The wrapper is intentionally **generic in `Event` and `State`**:
the canonical CJSV22 instantiation
(`Event := MomentaryCorruption.Alphabet Sid Pid`,
`State := MomentaryCorruption.State Sid Pid`)
is one consumer, but every other environment-driven effect
(broadcast resets, time advance, side-channel reseed,
environment-controlled randomness oracle) reuses the same wrapper
with different `(Event, State)` instantiations.

## What this file ships

The **wrapper data layer** only:

* `EnvOpenProcess` structure with `@[ext]`;
* projections `toOpenProcess`, `react`;
* canonical wrappings `ofOpenProcess` (empty alphabet) and
  `passive` (alphabet acts as identity);
* alphabet adaptation `comapEvent`, env-action replacement
  `withEnvAction`, boundary adaptation `mapBoundary`.

The composition operators (`par` / `wire` / `plug` lifted from
`OpenTheory`) are intentionally **not** here: lifting them requires
an explicit *combination strategy* for the env channels of the two
sub-wrappers (broadcast vs targeted vs Kleisli-sequential), which is
application-specific (Signal uses targeted routing keyed by
`MachineId`; broadcast resets use product). The operators are best
parameterized by the strategy rather than baked in. Composition,
forwarding lemmas decomposing env reactions on composites, and the
runtime integration that schedules env events alongside boundary
ticks all live in subsequent files.

The canonical CJSV22 instantiation `MomentaryCorruption.Process`
(and the bundled `MomentaryCorruption.model : CorruptionModel`
value) lives in `MomentaryCorruption.lean`.
-/

universe u uE v w w'

namespace Interaction
namespace UC

/--
`EnvOpenProcess m Party Δ Event State` is an `OpenProcess m Party Δ`
paired with an `EnvAction Event State` describing how an environment-side
state of type `State` evolves under environment events drawn from `Event`.

The two fields encode orthogonal effect channels:

* `process : OpenProcess m Party Δ` — the standard open-process boundary
  surface, with its own controllers, views, per-step nodewise sampler,
  and `BoundaryAction` for port traffic.
* `envAction : EnvAction Event State` — an independent env-driven
  channel for actions whose semantics are *not* port-routed (CJSV22
  §3.2 corruption, broadcast resets, time advance).

The state type `State` is constrained to `Type` (universe 0) because
`EnvAction.react` returns a `ProbComp State` and `ProbComp : Type → Type`.

Existing `OpenProcess` consumers are unaffected: nothing here is
threaded into `OpenNodeProfile`. The wrapper is the structural
foundation for corruption-aware composition and for the canonical
CJSV22 instantiation `MomentaryCorruption.Process` in
`MomentaryCorruption.lean`.
-/
@[ext]
structure EnvOpenProcess
    (m : Type w → Type w')
    (Party : Type u) (Δ : PortBoundary)
    (Event : Type uE) (State : Type) where
  /-- The underlying open process exposing the boundary `Δ`. -/
  process : OpenProcess.{u, v, w, w'} m Party Δ
  /-- The environment-event channel acting on `State` under `Event`. -/
  envAction : EnvAction Event State

namespace EnvOpenProcess

variable {m : Type w → Type w'} {Party : Type u} {Δ : PortBoundary}
  {Event : Type uE} {State : Type}

/-! ## Projections -/

/--
Forget the environment channel and view as a plain `OpenProcess`.

This is the canonical projection: it drops the env action and retains
only the open-process boundary surface.
-/
@[reducible]
def toOpenProcess (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State) :
    OpenProcess.{u, v, w, w'} m Party Δ := E.process

/--
React to an environment event on the env-side state, delegating to the
underlying `EnvAction.react`.

Provided as a top-level projection so that downstream consumers can
write `E.react e s` without unfolding the wrapper.
-/
def react (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (e : Event) (s : State) : ProbComp State :=
  E.envAction.react e s

@[simp]
theorem react_eq_envAction_react
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (e : Event) (s : State) :
    E.react e s = E.envAction.react e s := rfl

/-! ## Canonical wrappings -/

/--
Wrap an `OpenProcess` with the trivial empty alphabet: no environment
events ever fire.

This is the canonical no-op wrapping: every existing `OpenProcess`
embeds into `EnvOpenProcess _ _ Empty State` for any `State`.
-/
def ofOpenProcess
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type) :
    EnvOpenProcess.{u, 0, v, w, w'} m Party Δ Empty S where
  process := P
  envAction := EnvAction.empty S

@[simp]
theorem process_ofOpenProcess
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type) :
    (ofOpenProcess P S).process = P := rfl

@[simp]
theorem envAction_ofOpenProcess
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (S : Type) :
    (ofOpenProcess P S).envAction = EnvAction.empty S := rfl

/--
Wrap an `OpenProcess` with the passive alphabet: every event leaves the
state unchanged.

Useful when a process needs to participate in a non-trivial alphabet
(so its env-channel slot must be inhabited at the chosen `Event` /
`State` types) but its own state is unaffected by every event.
-/
def passive
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event S where
  process := P
  envAction := EnvAction.passive Event S

@[simp]
theorem process_passive
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type) :
    (passive P Event S).process = P := rfl

@[simp]
theorem envAction_passive
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type) :
    (passive P Event S).envAction = EnvAction.passive Event S := rfl

@[simp]
theorem react_passive
    (P : OpenProcess.{u, v, w, w'} m Party Δ) (Event : Type uE) (S : Type)
    (e : Event) (s : S) :
    (passive P Event S).react e s = pure s := rfl

/-! ## Alphabet and env-action adaptation -/

/--
Adapt the env alphabet along an event embedding `g : Event → Event'`.

The new wrapper accepts events of type `Event`; each such event `e` is
routed through `g` to obtain `g e : Event'` and passed to the original
env action. This is the contravariant action on the alphabet that lets
coarser alphabets be embedded into finer ones (e.g. lift a
`MomentaryCorruption.Alphabet` into a richer alphabet that also
tracks broadcast events).

The underlying open process is unchanged.
-/
def comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State where
  process := E.process
  envAction := E.envAction.comap g

@[simp]
theorem process_comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    (comapEvent g E).process = E.process := rfl

@[simp]
theorem envAction_comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State) :
    (comapEvent g E).envAction = E.envAction.comap g := rfl

@[simp]
theorem comapEvent_id
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State) :
    comapEvent (id : Event → Event) E = E := by
  cases E; simp [comapEvent]

@[simp]
theorem comapEvent_comapEvent {Event' Event'' : Type uE}
    (h : Event → Event') (g : Event' → Event'')
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event'' State) :
    comapEvent h (comapEvent g E) = comapEvent (g ∘ h) E := by
  cases E; simp [comapEvent]

/--
Replace the env action wholesale, retargeting the wrapper to a new
`(Event', State')` pair. The underlying open process is unchanged.

Used when the same open process needs to be paired with a different env
channel (e.g. lifting from the canonical `MomentaryCorruption.react`
reaction to a richer simulator-controlled reaction with its own state).
-/
def withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction Event' State') :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event' State' where
  process := E.process
  envAction := ea

@[simp]
theorem process_withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction Event' State') :
    (E.withEnvAction ea).process = E.process := rfl

@[simp]
theorem envAction_withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ Event State)
    (ea : EnvAction Event' State') :
    (E.withEnvAction ea).envAction = ea := rfl

/-! ## Boundary adaptation -/

/--
Adapt the underlying open process along a `PortBoundary.Hom`, leaving
the env channel intact.

The boundary action of the underlying process is translated forward
(emitted packets translated, activation flags preserved) along `φ`.
The env action is independent of the port boundary, so it is carried
through unchanged. This is the env-channel-aware analogue of
`OpenProcess.mapBoundary`.
-/
def mapBoundary {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₂ Event State where
  process := E.process.mapBoundary φ
  envAction := E.envAction

@[simp]
theorem process_mapBoundary {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    (E.mapBoundary φ).process = E.process.mapBoundary φ := rfl

@[simp]
theorem envAction_mapBoundary {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w, w'} m Party Δ₁ Event State) :
    (E.mapBoundary φ).envAction = E.envAction := rfl

end EnvOpenProcess

end UC
end Interaction

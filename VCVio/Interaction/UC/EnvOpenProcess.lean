/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.EnvAction

/-!
# Open processes paired with an environment-event channel

This file introduces `EnvOpenProcess Party Δ Event State`, the structural
pairing of an `OpenProcess Party Δ` with an `EnvAction Event State`. The
wrapper carries two orthogonal effect channels:

* the underlying `OpenProcess`'s **boundary channel** (port traffic
  between participants);
* a separate **environment channel** through which the environment fires
  events drawn from `Event` that act on a per-step state of type `State`.

The two channels are kept structurally orthogonal, matching CJSV22 §3.2
where corruption events flow from the environment rather than from the
adversary's port boundary. The wrapper is intentionally **generic in
`Event` and `State`**: the canonical CJSV22 instantiation
(`Event := CorruptionAlphabet Sid Pid`, `State := CorruptionState Sid Pid`)
is one consumer, but every other environment-driven effect (broadcast
resets, time advance, side-channel reseed, environment-controlled
randomness oracle) reuses the same wrapper.

## Why a separate wrapper instead of threading `Σ` into `OpenNodeSemantics`

The original F2 design memo (`vcvio-uc-f2-corruption-design.md` §3.1
Design A) proposed adding an `envAction : EnvAction Σ Δ X` field directly
on `OpenNodeSemantics`. That would force every existing `OpenProcess`
construction site to thread an additional universe and parameter, even
when `Σ := Empty`. The wrapper here ships the same expressive power
**additively**: existing `OpenProcess` consumers are unchanged, and the
env channel only appears for processes that explicitly opt in.

The wrapper is the structural ancestor of the corruption-aware
composition operators, scope policies, and forwarding lemmas (CJSV22
§4.2) that follow in subsequent slices.

## Slicing

This file ships the **wrapper data layer** only:

* `EnvOpenProcess` structure with `@[ext]`;
* projections `toOpenProcess`, `react`;
* canonical wrappings `ofOpenProcess` (empty alphabet) and
  `passive` (alphabet acts as identity);
* alphabet adaptation `comapEvent`, env-action replacement
  `withEnvAction`, boundary adaptation `mapBoundary`.

**Deferred to a follow-up slice:**

* Composition operators `par` / `wire` / `plug` lifted from
  `OpenTheory`. These require an explicit *combination strategy* for
  the env channels of the two sub-wrappers (broadcast vs targeted vs
  Kleisli-sequential). The strategy is application-specific (Signal
  uses targeted routing keyed by `MachineId`; broadcast resets use
  product), so the operators are best parameterized by the strategy
  rather than baked in here.
* The four `*.corrupt` forwarding lemmas (CJSV22 §4.2) and their
  generic `*.envReact` analogues, which decompose env reactions on
  composites in terms of reactions on the components.
* The runtime integration that schedules env events alongside boundary
  ticks (a small extension to `processSemanticsOracle` in
  `Runtime.lean`).

See `Notes/vcvio-uc-f2-corruption-design.md` for the full F2 roadmap
and `VCVio/Interaction/UC/Corruption.lean` for the canonical Signal
instantiation `CorruptionProcess`.
-/

universe u uE v w

namespace Interaction
namespace UC

/--
`EnvOpenProcess Party Δ Event State` is an `OpenProcess Party Δ` paired
with an `EnvAction Event State` describing how an environment-side state
of type `State` evolves under environment events drawn from `Event`.

The two fields encode orthogonal effect channels:

* `process : OpenProcess Party Δ` — the standard open-process boundary
  surface, with its own controllers, views, and `BoundaryAction` for
  port traffic.
* `envAction : EnvAction Event State` — an independent env-driven
  channel for actions whose semantics are *not* port-routed (CJSV22
  §3.2 corruption, broadcast resets, time advance).

The state type `State` is constrained to `Type` (universe 0) because
`EnvAction.react` returns a `ProbComp State` and `ProbComp : Type → Type`.

Existing `OpenProcess` consumers are unaffected: nothing here is
threaded into `OpenNodeSemantics`. The wrapper is the structural
foundation for corruption-aware composition (a subsequent slice) and
for the canonical Signal instantiation `CorruptionProcess` in
`Corruption.lean`.
-/
@[ext]
structure EnvOpenProcess
    (Party : Type u) (Δ : PortBoundary)
    (Event : Type uE) (State : Type) where
  /-- The underlying open process exposing the boundary `Δ`. -/
  process : OpenProcess.{u, v, w} Party Δ
  /-- The environment-event channel acting on `State` under `Event`. -/
  envAction : EnvAction Event State

namespace EnvOpenProcess

variable {Party : Type u} {Δ : PortBoundary}
  {Event : Type uE} {State : Type}

/-! ## Projections -/

/--
Forget the environment channel and view as a plain `OpenProcess`.

This is the canonical projection: it drops the env action and retains
only the open-process boundary surface.
-/
@[reducible]
def toOpenProcess (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State) :
    OpenProcess.{u, v, w} Party Δ := E.process

/--
React to an environment event on the env-side state, delegating to the
underlying `EnvAction.react`.

Provided as a top-level projection so that downstream consumers can
write `E.react e s` without unfolding the wrapper.
-/
def react (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State)
    (e : Event) (s : State) : ProbComp State :=
  E.envAction.react e s

@[simp]
theorem react_eq_envAction_react
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State)
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
    (P : OpenProcess.{u, v, w} Party Δ) (S : Type) :
    EnvOpenProcess.{u, 0, v, w} Party Δ Empty S where
  process := P
  envAction := EnvAction.empty S

@[simp]
theorem process_ofOpenProcess
    (P : OpenProcess.{u, v, w} Party Δ) (S : Type) :
    (ofOpenProcess P S).process = P := rfl

@[simp]
theorem envAction_ofOpenProcess
    (P : OpenProcess.{u, v, w} Party Δ) (S : Type) :
    (ofOpenProcess P S).envAction = EnvAction.empty S := rfl

/--
Wrap an `OpenProcess` with the passive alphabet: every event leaves the
state unchanged.

Useful when a process needs to participate in a non-trivial alphabet
(so its env-channel slot must be inhabited at the chosen `Event` /
`State` types) but its own state is unaffected by every event.
-/
def passive
    (P : OpenProcess.{u, v, w} Party Δ) (Event : Type uE) (S : Type) :
    EnvOpenProcess.{u, uE, v, w} Party Δ Event S where
  process := P
  envAction := EnvAction.passive Event S

@[simp]
theorem process_passive
    (P : OpenProcess.{u, v, w} Party Δ) (Event : Type uE) (S : Type) :
    (passive P Event S).process = P := rfl

@[simp]
theorem envAction_passive
    (P : OpenProcess.{u, v, w} Party Δ) (Event : Type uE) (S : Type) :
    (passive P Event S).envAction = EnvAction.passive Event S := rfl

@[simp]
theorem react_passive
    (P : OpenProcess.{u, v, w} Party Δ) (Event : Type uE) (S : Type)
    (e : Event) (s : S) :
    (passive P Event S).react e s = pure s := rfl

/-! ## Alphabet and env-action adaptation -/

/--
Adapt the env alphabet along an event embedding `g : Event → Event'`.

The new wrapper accepts events of type `Event`; each such event `e` is
routed through `g` to obtain `g e : Event'` and passed to the original
env action. This is the contravariant action on the alphabet that lets
coarser alphabets be embedded into finer ones (e.g. lift a
`CorruptionAlphabet` into a richer alphabet that also tracks broadcast
events).

The underlying open process is unchanged.
-/
def comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event' State) :
    EnvOpenProcess.{u, uE, v, w} Party Δ Event State where
  process := E.process
  envAction := E.envAction.comap g

@[simp]
theorem process_comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event' State) :
    (comapEvent g E).process = E.process := rfl

@[simp]
theorem envAction_comapEvent {Event' : Type uE}
    (g : Event → Event')
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event' State) :
    (comapEvent g E).envAction = E.envAction.comap g := rfl

@[simp]
theorem comapEvent_id
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State) :
    comapEvent (id : Event → Event) E = E := by
  cases E; simp [comapEvent]

@[simp]
theorem comapEvent_comapEvent {Event' Event'' : Type uE}
    (h : Event → Event') (g : Event' → Event'')
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event'' State) :
    comapEvent h (comapEvent g E) = comapEvent (g ∘ h) E := by
  cases E; simp [comapEvent]

/--
Replace the env action wholesale, retargeting the wrapper to a new
`(Event', State')` pair. The underlying open process is unchanged.

Used when the same open process needs to be paired with a different env
channel (e.g. lifting from the canonical `CorruptionState` reaction to a
richer simulator-controlled reaction with its own state).
-/
def withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State)
    (ea : EnvAction Event' State') :
    EnvOpenProcess.{u, uE, v, w} Party Δ Event' State' where
  process := E.process
  envAction := ea

@[simp]
theorem process_withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State)
    (ea : EnvAction Event' State') :
    (E.withEnvAction ea).process = E.process := rfl

@[simp]
theorem envAction_withEnvAction {Event' : Type uE} {State' : Type}
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ Event State)
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
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ₁ Event State) :
    EnvOpenProcess.{u, uE, v, w} Party Δ₂ Event State where
  process := E.process.mapBoundary φ
  envAction := E.envAction

@[simp]
theorem process_mapBoundary {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ₁ Event State) :
    (E.mapBoundary φ).process = E.process.mapBoundary φ := rfl

@[simp]
theorem envAction_mapBoundary {Δ₁ Δ₂ : PortBoundary}
    (φ : PortBoundary.Hom Δ₁ Δ₂)
    (E : EnvOpenProcess.{u, uE, v, w} Party Δ₁ Event State) :
    (E.mapBoundary φ).envAction = E.envAction := rfl

end EnvOpenProcess

end UC
end Interaction

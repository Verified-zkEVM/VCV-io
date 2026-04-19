/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp

/-!
# Environment-driven action alphabets

This file introduces `EnvAction Event X`, a typed channel for
environment-fired events that update a per-step state.

## Why a separate channel from `BoundaryAction`

`OpenProcess Party Δ` already has one effect channel: the
**boundary**, carrying port traffic *between participants* (Alice
sends a packet to the network, the network delivers to Bob). That
channel is the natural home for everything routed through ports.

But the environment can also act on a process directly, *without
going through any port*. In CJSV22 §3.2 the canonical example is
corruption: the environment may fire `compromise(m)` or
`refresh(m)` for a machine `m`, and crucially the adversary cannot
trigger this through Alice's input port. The same shape recurs
elsewhere: a global broadcast reset, a time-advance pulse, an
environment-controlled randomness reseed. None of these are
port-routed; all of them update bookkeeping state that the
adversary then observes.

`EnvAction` gives that pattern a typed home:

* `Event` is the alphabet of things the environment can fire (a
  user-supplied sum type, e.g.
  `compromise(m) | refresh(m) | broadcastReset`).
* `X` is the bookkeeping state the events mutate (corruption flags,
  epoch counters, broadcast clocks).
* `react : Event → X → ProbComp X` is the per-event reaction.

Pairing an `OpenProcess` with an `EnvAction` then keeps the two
channels structurally orthogonal: port traffic through
`BoundaryAction`, environment effects through `EnvAction`. The
pairing is `EnvOpenProcess` in `EnvOpenProcess.lean`.

## "Env" vs "Event"

The naming `EnvAction Event X` is asymmetric on purpose:

* **`Env`** (in the type name) names *who* fires the action — the
  environment, in the UC sense (one level above the adversary in
  the CJSV22 universe; not adversary-accessible directly).
* **`Event`** (the alphabet parameter) names *what* they fire.

So `EnvAction Event X` reads as "actions fired by the environment,
drawn from the `Event` alphabet, mutating state of type `X`". The
two are not redundant: `Env` carries security-relevant routing info
(env-only, not adversary-accessible), `Event` is just the algebra
of messages.

The alphabet parameter is named `Event` rather than the CJSV22-style
`Σ` because `Σ` is a reserved Lean keyword (sigma types). The CSP /
π-calculus convention "events" is also a more literal description of
what the alphabet contains than the bare letter `Σ`.

## Probabilistic reactions

`react` is `ProbComp`-valued, so environment-driven state
transitions can themselves be probabilistic (e.g.
simulator-controlled randomization on `compromise`). Deterministic
events use `pure ∘ update` and pay no extra cost.

## Additive design

`EnvAction` is intentionally **standalone**: it is *not* threaded
into `OpenNodeProfile`. Existing `OpenProcess Party Δ`
constructions are unaffected, and protocols that do not need
environment-driven events incur zero cost. The corruption-aware
wrapper that pairs an `OpenProcess` with a state-indexed
`EnvAction` lives in `EnvOpenProcess.lean`; the canonical CJSV22
instantiation (corruption with refresh-based healing) lives in
`MomentaryCorruption.lean`.
-/

/-
The state type `X` is constrained to `Type 0` because `ProbComp : Type → Type`
lives in `Type`. This matches the universe convention in
`VCVio/Interaction/UC/Runtime.lean`, where the runtime layer requires move
and state types to live in `Type 0` for the same reason.
-/
universe u

namespace Interaction
namespace UC

/--
`EnvAction Event X` is the per-event reaction of a per-step state
`x : X` to environment events drawn from the alphabet `Event`.

`react : Event → X → ProbComp X` specifies how each event transforms
the state. The default `react` is `fun _ x => pure x` (every event is
a no-op), which keeps the empty alphabet `Event := Empty` trivially
satisfiable.

Two concrete instantiations matter here:

* `EnvAction Empty X` — the trivial alphabet, used by every protocol
  that doesn't participate in environment-driven corruption. Costs
  nothing; the canonical inhabitant is `EnvAction.empty`.
* `EnvAction (MomentaryCorruption.Alphabet Sid Pid)
  (MomentaryCorruption.State Sid Pid)` — the canonical CJSV22
  instantiation. See `VCVio.Interaction.UC.MomentaryCorruption` for
  the alphabet and state definitions.

The structure is independent of the boundary `Δ` so that environment
events are *not* keyed by port: an environment event acts on whatever
`X`-typed slice of state the protocol exposes, with no dependence on
which ports happen to be in scope.
-/
@[ext]
structure EnvAction (Event : Type u) (X : Type) where
  /-- The state transition triggered by each event. -/
  react : Event → X → ProbComp X := fun _ x => pure x

namespace EnvAction

variable {Event : Type u} {X : Type}

/--
The trivial environment-action over the empty alphabet: no events
ever fire.

Useful as the default for processes that do not care about
environment-driven dynamics.
-/
def empty (X : Type) : EnvAction Empty X where
  react e _ := e.elim

/--
The constant environment-action: every event leaves the state
unchanged.

This is the canonical "passive observer" reaction, useful when a
process participates in an alphabet (so its `EnvAction` slot is
non-trivially typed) but its state has no per-event update.
-/
def passive (Event : Type u) (X : Type) : EnvAction Event X where
  react _ x := pure x

/--
Adapt the alphabet of an environment-action along a function
`g : Event → Event'`.

The new alphabet is `Event`; an event `s : Event` is reacted to by
routing it through `g` to obtain `s' : Event'` and applying the
original reaction. This is the contravariant action on the alphabet
that lets coarser alphabets be embedded into finer ones.
-/
def comap {Event Event' : Type u} {X : Type}
    (g : Event → Event') (e : EnvAction Event' X) : EnvAction Event X where
  react s x := e.react (g s) x

/--
Adapt the state of an environment-action along a state-projection.

Given `e : EnvAction Event X` and a projection `π : Y → X` together
with a re-installation `ι : X → Y → Y` that re-installs the updated
`X` slice into a larger state `Y`, the lifted action operates on `Y`
by reacting on the `X`-slice and re-installing the result.

This is the structural lift used when corruption-aware reactions need
to thread through richer per-step states; the `MomentaryCorruption`
layer uses it to lift the canonical `MomentaryCorruption.react` over
state-bundled `MachineProcess`es.
-/
def liftState {Event : Type u} {X Y : Type}
    (π : Y → X) (ι : X → Y → Y) (e : EnvAction Event X) :
    EnvAction Event Y where
  react s y := do
    let x' ← e.react s (π y)
    return ι x' y

@[simp]
theorem comap_id (e : EnvAction Event X) :
    comap (id : Event → Event) e = e := by
  ext s x; rfl

@[simp]
theorem comap_comap {Event Event' Event'' : Type u} {X : Type}
    (h : Event → Event') (g : Event' → Event'') (e : EnvAction Event'' X) :
    comap h (comap g e) = comap (g ∘ h) e := by
  ext s x; rfl

@[simp]
theorem passive_react (Event : Type u) (X : Type) (s : Event) (x : X) :
    (passive Event X).react s x = pure x := rfl

@[simp]
theorem empty_react (X : Type) (e : Empty) (x : X) :
    (empty X).react e x = e.elim := rfl

end EnvAction

end UC
end Interaction

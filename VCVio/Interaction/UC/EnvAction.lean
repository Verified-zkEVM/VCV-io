/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp

/-!
# Environment-driven action alphabets

This file introduces `EnvAction Sym X`, a standalone alphabet of
environment-driven events that may act on a per-step state of type `X`.
The alphabet `Sym` is the user-supplied symbol set (typically a sum
type with one constructor per environment event: `compromise`,
`refresh`, `setEpochParam`, etc.); the `react` function specifies how
the state evolves on each event.

This vocabulary is the foundation for CJSV22-style adaptive momentary
corruption (Canetti, Jain, Swanberg, Varia, *Universally Composable
End-to-End Secure Messaging*, CRYPTO 2022 §3.2). In CJSV22 the
environment is the privileged source of `Corrupt`-type events, distinct
from the adversary boundary (which carries port traffic). `EnvAction`
gives the same separation a typed home in VCVio: corruption events flow
through `EnvAction`, port traffic flows through `BoundaryAction`, and
the two channels are kept structurally orthogonal.

The alphabet parameter is named `Sym` rather than the CJSV22-style
`Σ` because `Σ` is a reserved Lean keyword (sigma types).

## Additive design

`EnvAction` is intentionally **standalone**: it is *not* threaded into
`OpenNodeSemantics` in this slice. Existing `OpenProcess Party Δ`
constructions are unaffected, and protocols that do not need
environment-driven events incur zero cost. A subsequent slice will
build a corruption-aware wrapper that pairs an `OpenProcess` with a
state-indexed `EnvAction`; the four `*.corrupt` forwarding lemmas
(CJSV22 §4.2) live on that wrapper.

## Probabilistic reactions

`react` is `ProbComp`-valued, so corruption-driven state transitions
can themselves be probabilistic (e.g. simulator-controlled
randomization on `compromise`). Deterministic events use
`pure ∘ update` and pay no extra cost.
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
`EnvAction Sym X` is the per-event reaction of a per-step state
`x : X` to environment events drawn from the alphabet `Sym`.

`react : Sym → X → ProbComp X` specifies how each event transforms
the state. The default `react` is `fun _ x => pure x` (every event is
a no-op), which keeps the empty alphabet `Sym := Empty` trivially
satisfiable.

Two concrete instantiations matter here:

* `EnvAction Empty X` — the trivial alphabet, used by every protocol
  that doesn't participate in environment-driven corruption. Costs
  nothing; the canonical inhabitant is `EnvAction.empty`.
* `EnvAction (CorruptionAlphabet Sid Pid) (CorruptionState Sid Pid)` —
  the canonical CJSV22 instantiation. See
  `VCVio.Interaction.UC.Corruption` for the alphabet and state
  definitions.

The structure is independent of the boundary `Δ` so that environment
events are *not* keyed by port: an environment event acts on whatever
`X`-typed slice of state the protocol exposes, with no dependence on
which ports happen to be in scope.
-/
@[ext]
structure EnvAction (Sym : Type u) (X : Type) where
  /-- The state transition triggered by each event. -/
  react : Sym → X → ProbComp X := fun _ x => pure x

namespace EnvAction

variable {Sym : Type u} {X : Type}

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
def passive (Sym : Type u) (X : Type) : EnvAction Sym X where
  react _ x := pure x

/--
Adapt the alphabet of an environment-action along a function
`g : Sym → Sym'`.

The new alphabet is `Sym`; an event `s : Sym` is reacted to by routing
it through `g` to obtain `s' : Sym'` and applying the original
reaction. This is the contravariant action on the alphabet that lets
coarser alphabets be embedded into finer ones.
-/
def comap {Sym Sym' : Type u} {X : Type}
    (g : Sym → Sym') (e : EnvAction Sym' X) : EnvAction Sym X where
  react s x := e.react (g s) x

/--
Adapt the state of an environment-action along a state-projection.

Given `e : EnvAction Sym X` and a projection `π : Y → X` together with
a re-installation `ι : X → Y → Y` that re-installs the updated `X`
slice into a larger state `Y`, the lifted action operates on `Y` by
reacting on the `X`-slice and re-installing the result.

This is the structural lift used when corruption-aware reactions need
to thread through richer per-step states; the `Corruption` layer uses
it to lift the canonical `CorruptionState.react` over state-bundled
`MachineProcess`es.
-/
def liftState {Sym : Type u} {X Y : Type}
    (π : Y → X) (ι : X → Y → Y) (e : EnvAction Sym X) :
    EnvAction Sym Y where
  react s y := do
    let x' ← e.react s (π y)
    return ι x' y

@[simp]
theorem comap_id (e : EnvAction Sym X) :
    comap (id : Sym → Sym) e = e := by
  ext s x; rfl

@[simp]
theorem comap_comap {Sym Sym' Sym'' : Type u} {X : Type}
    (h : Sym → Sym') (g : Sym' → Sym'') (e : EnvAction Sym'' X) :
    comap h (comap g e) = comap (g ∘ h) e := by
  ext s x; rfl

@[simp]
theorem passive_react (Sym : Type u) (X : Type) (s : Sym) (x : X) :
    (passive Sym X).react s x = pure x := rfl

@[simp]
theorem empty_react (X : Type) (e : Empty) (x : X) :
    (empty X).react e x = e.elim := rfl

end EnvAction

end UC
end Interaction

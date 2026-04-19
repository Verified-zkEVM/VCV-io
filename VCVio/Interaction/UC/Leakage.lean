/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Leakage observation models

This file defines typeclasses that capture **how the adversary
observes a corrupted party's secrets**. Leakage is orthogonal to the
choice of `CorruptionModel` (the alphabet of corruption events plus
the bookkeeping state); a single corruption model can be paired with
several leakage observers in different proofs.

Concretely, when the environment fires a corruption event such as
`compromise(m)`, the framework asks: *what does the adversary now
learn about machine `m`?* Different observation models give different
answers:

* **Snapshot leak** (`SnapshotLeakable`) — at corruption time, the
  adversary receives a **static projection** of the current
  protocol state for `m`. Most CJSV22-style proofs use this. Keys,
  ratchet roots, and counters can all be projected; ephemeral chat
  contents typically cannot. This is the only observer formalised
  in this file.
* **Interactive leak** (planned) — the adversary issues *queries*
  against the live protocol state of `m` while corruption is
  active. Captures models where the adversary can probe arbitrary
  computable functions of the secret state.
* **Erasure-aware** (planned) — the adversary only learns the
  *un-erased* portion of `m`'s state at corruption time. Captures
  proactive-erasure protocols where applications proactively zero
  out long-term secrets after use.
* **Structured / partial** (planned) — leakage is mediated by a
  chosen lattice (`StructuredLeakable`); applications declare which
  sub-projections each level reveals. Useful for side-channel
  models with bounded leakage budget.
* **Passive / no leak** — corruption affects bookkeeping only, the
  adversary learns nothing further from the live state. Captured by
  the *absence* of any leakage instance.

Each observer is a separate typeclass; a protocol declares the
appropriate instance (or no instance, for the passive case) and the
security definition consumes it. Mixing observers across composites
is handled at the composition layer, not here.

## Why a typeclass and not a `CorruptionModel` field

Bundling leakage into `CorruptionModel` would force every consumer
of the model to commit to one observer up front. In practice the
same model (e.g. `MomentaryCorruption.model`) appears with several
observers across different proofs: a ROM-style snapshot leak in
the IND-CCA proof, a structured leak in the side-channel reduction.
Making leakage a separately-resolved typeclass keeps the model
reusable.

## Why no default instance for `SnapshotLeakable`

A default instance would either leak too much (project the entire
`State`, breaking forward-secrecy proofs) or too little (project
nothing, vacuously satisfying the typeclass and rendering the
adversary blind). Forcing every protocol to declare what it leaks
turns the equivocability obligation into a missing-instance error
rather than a meta-theoretic side condition.
-/

universe u

namespace Interaction
namespace UC

/--
`SnapshotLeakable State Leakage` exposes a static **per-party
projection** of the protocol state, fired at corruption time.

* `State` — the live protocol state being projected.
* `Party` — the party identity whose secrets are being leaked
  (typically `MachineId Sid Pid` for CJSV22-style proofs, but the
  class is intentionally agnostic).
* `Leakage` — the projection's payload type.

The class encodes the **snapshot leakage observer**: at the moment
of corruption, the adversary receives `leak σ p : Leakage` for the
target party `p`. The function is *static*: it fires once per
corruption event and ignores any subsequent live activity on
`p`. For interactive observers (the adversary issues live queries
against the corrupted state), use a future `InteractiveLeakable`.

`Leakage` is an `outParam` because each `(State, Party)` pair
functionally determines its leakage type: there is one canonical
projection per protocol, and ambiguity should not arise during
instance synthesis.

The intended use is on `MachineProcess`-shaped state types: a real
protocol supplies the natural projection (e.g. "current long-term
secret + ratchet root for party `p`"); a simulator supplies a
fabrication consistent with all prior leakages and the current
adversary trace. By exposing the obligation as a typeclass, the
framework forces the following invariant at compile time: a
simulator that cannot fabricate consistent state cannot supply an
instance, and cannot be plugged into the security definition.

This is the typed form of the **equivocability obligation** from
CJSV22 §4.1.

There is **no default instance**. See the module docstring for why.
-/
class SnapshotLeakable
    {Party : Type u} (State : Type) (Leakage : outParam Type) where
  /-- Project a per-party snapshot from `State` at corruption time. -/
  leak : State → Party → Leakage

end UC
end Interaction

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.Examples.Signal.Atoms
import VCVio.Interaction.UC.Examples.Signal.Boundaries

/-!
# `F_DoubleRatchet`: ideal Signal Double-Ratchet functionality (skeleton)

`F_DoubleRatchet` packages the two-party Double-Ratchet ideal
functionality as an `OpenProcess Party Δ_signal`. Phase 0 supplies
*types only*: the residual state space, the boundary it exposes, and
a trivial honest step body so that the construction typechecks
end-to-end.

## What is filled in at Phase 0

* `Proc := SessionState × SessionState`, holding Alice's and Bob's
  Double-Ratchet state side by side. The ordering matches the tensor
  factorization `Δ_signal = Δ_alice ⊗ᵇ Δ_bob`.
* `step` is the honest no-op step `honestNoopStep`: each tick
  immediately terminates, consumes no inputs, emits no packets, and
  leaves the state unchanged. This is sufficient for the type
  obligation and serves as the placeholder that Phase 1 will replace
  with real send/receive semantics.

## What is intentionally `sorry`

* `corruptLeakStep` is the placeholder for the corrupt-leak step body
  (the adversary requests a state snapshot via the `AdvIn.corrupt`
  port and the functionality answers on `AdvOut.leakState`).
  Implementing it faithfully requires three currently-missing
  framework pieces:

  - input-side query decoding inside `BoundaryAction` (so that the
    spec body can branch on the *port* on which an incoming packet
    arrives);
  - a `CorruptionPolicy` recording which parties are currently
    compromised;
  - per-node corruption flags inside `NodeSemantics` (so reductions
    can quantify over honest-only or corrupt-aware traces).

  These three gaps are tracked at the top of the milestones document
  and will be addressed before Phase 1 attempts the first emulation
  statement.

There are **no axioms** in this module. Every unproven assumption is
either represented as a `sorry` placeholder (currently only
`corruptLeakStep`) or pushed out to a structure parameter that will
be supplied by future phases.
-/

namespace Interaction
namespace UC
namespace Examples
namespace Signal

open Interaction.UC

/-! ### Residual state -/

/-- The residual state held by `F_DoubleRatchet`: Alice's session
state on the left, Bob's on the right. -/
abbrev DRState : Type := SessionState × SessionState

/-! ### Step bodies -/

/-- Honest no-op step.

The functionality immediately returns control to the scheduler with
the session state unchanged, no inputs consumed, and no packets
emitted on either party's outgoing boundary.

Phase 1 will replace this with the actual symmetric- and asymmetric-
ratchet behavior: on each scheduled tick the functionality reads the
next pending packet on the appropriate port (application send,
network receive, or network send acknowledgement) and updates the
relevant party's `SessionState` accordingly. -/
def honestNoopStep (st : DRState) :
    Concurrent.StepOver
      (OpenStepContext Party Δ_signal : Spec.Node.Context.{0}) DRState where
  spec := .done
  semantics := ⟨⟩
  next := fun _ => st

/-- Corrupt-leak step (deferred).

Intentionally `sorry` at Phase 0. A faithful implementation needs:

1. an input-decoding facility on `BoundaryAction` so that the spec
   can branch on an incoming `AdvIn.corrupt` packet (today
   `BoundaryAction` exposes only `isActivated : Bool` and an output
   emitter, with no first-class way to inspect *which* incoming port
   triggered activation; see `OpenProcess.lean` lines 60–66 for the
   acknowledgement of this gap);
2. a corruption policy associating each `Party` with a Boolean
   "currently compromised" flag whose evolution is tracked through
   the process;
3. per-node corruption flags inside `NodeSemantics` so that
   honest-only and corrupt-aware traces can be distinguished by the
   downstream simulator and by reduction proofs.

This declaration is not currently used by `F_DoubleRatchet`; it is
kept here to make the deferred design point trackable from a single
`sorry`. -/
def corruptLeakStep (st : DRState) :
    Concurrent.StepOver
      (OpenStepContext Party Δ_signal : Spec.Node.Context.{0}) DRState :=
  sorry

/-! ### The functionality

The `OpenProcess` is built directly from `honestNoopStep`. This
gives a typecheckable artifact that exposes the intended boundary
`Δ_signal` and carries the intended residual state, ready to be
extended with real protocol behavior in Phase 1.
-/

/-- The Phase 0 skeleton of the ideal Double-Ratchet functionality. -/
def F_DoubleRatchet : OpenProcess Party Δ_signal where
  Proc := DRState
  step := honestNoopStep

end Signal
end Examples
end UC
end Interaction

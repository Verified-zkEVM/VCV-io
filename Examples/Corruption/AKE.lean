/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.AsyncRuntime
import VCVio.Interaction.UC.MomentaryCorruption
import VCVio.Interaction.UC.Computational

/-!
# Two-party Diffie-Hellman ratchet AKE

A typed sketch of an authenticated key-exchange (AKE) protocol built
from a Diffie-Hellman ratchet, instantiated against the asynchronous
runtime layer (`AsyncRuntime.lean`) and the canonical adaptive-corruption
model (`MomentaryCorruption.lean`).

The file is **interface-only**: protocol bodies are `sorry`-skeletons
and the headline theorem is a `sorry`-statement. The point is to
exhibit, in one place, the type signatures connecting

* a concrete `MomentaryCorruption.Process` instance for a real protocol
  (`real`) and its ideal functionality (`ideal`);
* an async `Semantics` (`asyncSemantics`) that runs them under the
  canonical momentary-corruption env channel via
  `processSemanticsAsyncProbComp`;
* a `CompEmulates` security claim against arbitrary plugged
  environments, capturing post-compromise security after a refresh.

A full proof is deferred to a downstream milestone: a hybrid argument
indexed by epoch counter, with each per-epoch step bounded by DDH and
the union bound staying negligible because `fuel` bounds the number
of epochs in any one execution.

## Identity scheme

* `Sid := Unit` — single AKE session.
* `Pid := Bool` — two parties (`false ↦ Alice`, `true ↦ Bob`).
* `Party := MachineId Unit Bool` — the underlying open process's
  party type, induced by the canonical
  `MomentaryCorruption.Process Sid Pid Δ` wrapping.

## Boundary

`Δ_AKE` carries the parties' DH shares plus authentication tags.
The boundary is stubbed as `PortBoundary.empty` here; the concrete
shape is filled in alongside the protocol step function.

## Universe constraints

All identity types are at universe `0` (`Unit`, `Bool`,
`MachineId Unit Bool`), matching `MomentaryCorruption.Process`'s
universe-`0` constraint and the async runtime's universe-`0`
requirement on the runtime monad's argument types.
-/

universe v w

open Interaction Interaction.UC

namespace Examples.Corruption.AKE

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Boundary and ratchet state -/

/--
The AKE network boundary.

Carries a per-direction packet channel for the parties' DH shares plus
authentication tags. Stubbed as `PortBoundary.empty` in this sketch;
the concrete `Interface` instances are filled in alongside the
protocol step function.
-/
def Δ_AKE : PortBoundary := PortBoundary.empty

/--
Per-party ratchet bookkeeping.

Each party tracks a current ratchet key (or a sentinel default before
the first ratchet) plus a per-party epoch counter that advances under
`refresh(m)` events delivered through the env channel.

The ratchet state lives in the *process state* (the `Proc` field of
the underlying `MachineProcess`), not the env state, so that the env
channel stays generic across protocols and the only thing the
canonical momentary-corruption env action manipulates is the
corruption bookkeeping.
-/
structure SessionKeys (G : Type) where
  /-- Alice's current ratchet key. -/
  aliceKey : G
  /-- Bob's current ratchet key. -/
  bobKey : G
  /-- The ratchet epoch (synchronized between the two parties in the
  honest case; may diverge under attack). -/
  epoch : ℕ

namespace SessionKeys

/-- The fresh initial ratchet state: both parties hold the default
group element and the ratchet is at epoch zero. -/
def init (G : Type) [Inhabited G] : SessionKeys G :=
  ⟨default, default, 0⟩

instance (G : Type) [Inhabited G] : Inhabited (SessionKeys G) :=
  ⟨init G⟩

end SessionKeys

/-! ## Real and ideal protocols -/

/--
The real 2-party DH-ratchet AKE.

Wraps an underlying `MachineProcess Unit Bool Δ_AKE` whose step
function performs DH key derivation, ratchet advance, and
authentication-tag verification. The env channel is the canonical
momentary-corruption channel
(`MachineProcess.withMomentaryCorruption`).

Body left as `sorry`; the concrete step function is filled in
alongside the headline-proof obligation.
-/
noncomputable def real (_g : G) :
    MomentaryCorruption.Process.{0, 0, 0} Unit Bool ProbComp Δ_AKE :=
  sorry

/--
The ideal AKE functionality.

Emits a fresh, independent group element on every successful ratchet
round, regardless of the underlying DH structure. The env channel is
again the canonical momentary corruption channel, so the simulator's
consistency obligations are localized in the *plug* (the environment
chosen by `CompEmulates`'s quantifier), not in the env action itself.

Body left as `sorry`; the concrete ideal functionality is filled in
alongside its simulator.
-/
noncomputable def ideal (_g : G) :
    MomentaryCorruption.Process.{0, 0, 0} Unit Bool ProbComp Δ_AKE :=
  sorry

/--
The canonical scheduler sampler for this AKE pilot: the trivial
`ProbComp` computation returning `ULift.up true`. Any concrete choice
would do; this one is the simplest. -/
noncomputable def demoSchedulerSampler : ProbComp (ULift Bool) :=
  pure (ULift.up true)

/-! ## Async semantics -/

/--
The async semantics under which the AKE pilot is judged.

Instantiates `processSemanticsAsyncProbComp` at:

* the canonical momentary-corruption env channel
  (`MomentaryCorruption.envAction`);
* a fresh initial corruption state (`MomentaryCorruption.State.init`);
* a fuel parameter bounding the number of ticks in any one execution.

The remaining quantified arguments (`init`, `procScheduler`,
`envScheduler`, `observe`) are treated abstractly: a full use site of
`CompEmulates` against this semantics resolves them to the values
chosen by the plug it quantifies over.

Body left as `sorry`; concrete instantiations of the four schedulers
and the observer are filled in alongside the headline proof.
-/
noncomputable def asyncSemantics (_g : G) (_fuel : ℕ) :
    Semantics (openTheory.{0, 0, 0, 0} (MachineId Unit Bool)
      ProbComp demoSchedulerSampler) :=
  sorry

/-! ## Headline security claim -/

/--
The pilot security claim: the real DH-ratchet AKE computationally
emulates the ideal AKE up to advantage `ε` against every plug, when
judged by `asyncSemantics g fuel`.

The intended `ε` is the DDH distinguishing advantage of a particular
reduction adversary built from the plug. For a single hybrid step,
`ε ≤ ddhDistAdvantage g (someReduction)`; for a hybrid argument
indexed by epoch counter, `ε ≤ fuel * ddhDistAdvantage g (someReduction)`.

Body left as `sorry`; the proof is the canonical Phase 1 deliverable
of the milestone roadmap.
-/
theorem real_compEmulates_ideal_after_refresh
    (g : G) (fuel : ℕ) (ε : ℝ) :
    CompEmulates (asyncSemantics g fuel) ε
      (real g).process (ideal g).process :=
  sorry

end Examples.Corruption.AKE

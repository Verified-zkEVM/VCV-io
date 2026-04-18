/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.Examples.Signal.Atoms
import VCVio.Interaction.UC.Examples.Signal.Boundaries

/-!
# `F_DoubleRatchet`: ideal Signal Double-Ratchet functionality

`F_DoubleRatchet` packages the two-party Double-Ratchet ideal
functionality as an `OpenProcess Party Δ_signal`.

At each tick the functionality runs one short sequential episode that
consumes a single inbound packet on the combined boundary
`Δ_signal.In`, dispatches on the originating party (Alice or Bob) and
on the per-party port (application send, network receive, application
init, adversary corrupt), and emits the corresponding output packets
on `Δ_signal.Out`. The structural input-side decoding lives in the
new `BoundaryAction.inputDecode` field; the runtime feeds each
inbound packet through that decoder to obtain the local move that
the spec body then consumes.

## Phase-0 protocol behavior

Phase 0 stops short of modeling actual Double-Ratchet cryptography.
The skeleton implementation:

* on `AppCmd.send (peer, pt)`: bumps `sendIdx` for the sending party
  and emits one `NetOut.send (peer, pt, [])` packet (ciphertext is
  the plaintext, AD is empty);
* on `NetIn.recv (ct, _ad)`: bumps `recvIdx` for the receiving party
  and emits one `AppEvt.delivered (default, ct)` packet (the sender
  identity is a zero placeholder, the plaintext is the ciphertext);
* on `AppCmd.init`: leaves the state unchanged (real key-agreement
  initialization is deferred);
* on `AdvIn.corrupt`: flips the per-party `corrupted` flag and emits
  one `AdvOut.leakState ss` packet carrying the *current* per-party
  `SessionState` snapshot.

The protocol semantics is honest by default; corruption is recorded
in protocol-local state (the `SessionState.corrupted` flag) rather
than via a framework-level `CorruptionPolicy`. A framework-level
policy is the natural place for cross-functionality corruption
tracking and is the deferred Phase-1+ extension.

## What is *not* yet modeled

* No actual encryption / decryption: ciphertexts are plaintexts at
  Phase 0. Replacing this with a real ratchet KDF chain belongs to
  Phase 2.
* No internal routing of `NetOut.send` packets to the peer's
  `NetIn.recv` port. Such routing belongs to a network functionality
  composed alongside `F_DoubleRatchet`, not to `F_DoubleRatchet`
  itself.
* No simulator yet; the corresponding emulation statement
  (`F_DoubleRatchet ⊑ π_Signal`) is the Phase-1 deliverable.

There are **no axioms and no `sorry`s** in this module.
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

/-! ### Per-party event handlers

The following helpers operate on a *single* party's view of the
boundary: their input port and message type live in `signalInIface`,
not yet the combined `Δ_signal.In`. The party-dispatch (Alice vs Bob)
happens one level up in `step` below.
-/

namespace F_DoubleRatchet

/-- Update one party's `SessionState` in response to one per-party
input packet. -/
def applyPartyInput :
    (port : signalInIface.A) → signalInIface.B port → SessionState → SessionState
  | Sum.inl AppCmd.send, _, ss =>
      { ss with sendIdx := ss.sendIdx + 1 }
  | Sum.inl AppCmd.init, _, ss =>
      ss
  | Sum.inr (Sum.inl NetIn.recv), _, ss =>
      { ss with recvIdx := ss.recvIdx + 1 }
  | Sum.inr (Sum.inr AdvIn.corrupt), _, ss =>
      { ss with corrupted := true }

/-- Emit one party's outbound packets in response to one per-party
input packet. The output port indices follow the same `signalOutIface`
sum decomposition used by `signalInIface`. -/
def emitPartyOutput :
    (port : signalInIface.A) → signalInIface.B port → SessionState →
      List (Interface.Packet signalOutIface)
  | Sum.inl AppCmd.send, ⟨peer, pt⟩, _ss =>
      [⟨Sum.inr (Sum.inl NetOut.send), peer, pt, []⟩]
  | Sum.inl AppCmd.init, _, _ss =>
      []
  | Sum.inr (Sum.inl NetIn.recv), ⟨ct, _ad⟩, _ss =>
      [⟨Sum.inl AppEvt.delivered, (0 : Identity), ct⟩]
  | Sum.inr (Sum.inr AdvIn.corrupt), _, ss =>
      [⟨Sum.inr (Sum.inr AdvOut.leakState), ss⟩]

/-! ### Combined-boundary helpers -/

/-- Update the residual state in response to one combined-boundary
input packet. -/
def updateState (st : DRState) (pkt : Interface.Packet Δ_signal.In) : DRState :=
  match pkt with
  | ⟨Sum.inl partyPort, msg⟩ =>
      (applyPartyInput partyPort msg st.fst, st.snd)
  | ⟨Sum.inr partyPort, msg⟩ =>
      (st.fst, applyPartyInput partyPort msg st.snd)

/-- Emit the combined-boundary outputs in response to one
combined-boundary input packet. The per-party output packets are
injected into the appropriate summand of `Δ_signal.Out`. -/
def emitOutputs (st : DRState) (pkt : Interface.Packet Δ_signal.In) :
    List (Interface.Packet Δ_signal.Out) :=
  match pkt with
  | ⟨Sum.inl partyPort, msg⟩ =>
      (emitPartyOutput partyPort msg st.fst).map
        (Interface.Hom.mapPacket (Interface.Hom.inl signalOutIface signalOutIface))
  | ⟨Sum.inr partyPort, msg⟩ =>
      (emitPartyOutput partyPort msg st.snd).map
        (Interface.Hom.mapPacket (Interface.Hom.inr signalOutIface signalOutIface))

/-! ### Boundary action and node semantics -/

/-- The boundary action recorded at the single spec node of one
`F_DoubleRatchet` step.

* The node is *activated* by every inbound packet (the runtime
  delivers external traffic to it).
* `inputDecode` is the identity: each inbound packet *is* the local
  move at this node. Higher-level dispatch on the port is performed
  by `updateState` and `emitOutputs`.
* `emit` is computed against the *current* residual state `st`,
  which is captured by the closure of `step`. -/
def boundary (st : DRState) :
    BoundaryAction Δ_signal (Interface.Packet Δ_signal.In) where
  isActivated := true
  inputDecode pkt := some pkt
  emit pkt := emitOutputs st pkt

/-- The closed-world node semantics for the single spec node of one
`F_DoubleRatchet` step.

* `controllers` records the *originating* party of the inbound packet.
* `views` is uniformly `.observe` at Phase 0: both parties simply
  observe the global move (no information-hiding modeling yet).
-/
def nodeSem : Concurrent.NodeSemantics Party (Interface.Packet Δ_signal.In) where
  controllers pkt :=
    match pkt.fst with
    | Sum.inl _ => [Party.alice]
    | Sum.inr _ => [Party.bob]
  views _ := Multiparty.LocalView.observe

/-- Open node semantics: closed semantics + boundary action. -/
def openSem (st : DRState) :
    OpenNodeSemantics Party Δ_signal (Interface.Packet Δ_signal.In) where
  toNodeSemantics := nodeSem
  boundary := boundary st

/-! ### One step of the functionality -/

/-- One step of `F_DoubleRatchet`: consume a single inbound packet,
update the residual state, and emit the corresponding outputs.

The spec is a single-round episode `(.node (Packet Δ_signal.In)
(fun _ => .done))`; the only node carries the open-world boundary
action above; and `next` advances the residual state via
`updateState`. -/
def step (st : DRState) :
    Concurrent.StepOver
      (OpenStepContext Party Δ_signal : Spec.Node.Context.{0}) DRState where
  spec := .node (Interface.Packet Δ_signal.In) (fun _ => .done)
  semantics := ⟨openSem st, fun _ => ⟨⟩⟩
  next := fun ⟨pkt, _⟩ => updateState st pkt

end F_DoubleRatchet

/-! ### The functionality -/

/-- The Phase-0 ideal Double-Ratchet functionality.

The residual state is the pair of per-party `SessionState`s; each
step consumes one inbound packet on `Δ_signal.In`, dispatches on the
originating party and port, updates the corresponding per-party
state, and emits the appropriate per-party output packets on
`Δ_signal.Out`. -/
def F_DoubleRatchet : OpenProcess Party Δ_signal where
  Proc := DRState
  step := F_DoubleRatchet.step

end Signal
end Examples
end UC
end Interaction

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.Interface
import VCVio.Interaction.UC.Notation
import VCVio.Interaction.UC.Examples.Signal.Atoms

/-!
# Signal protocol — boundaries

The communication boundaries that the Double-Ratchet ideal
functionality and protocol expose. Each party owns a triple of
sub-interfaces:

* an **application** sub-interface (`signalApp{In,Out}Iface`) for
  user-level commands such as `send msg` and event deliveries such
  as `received plaintext`;
* a **network** sub-interface (`signalNet{In,Out}Iface`) for
  ciphertext traffic in and out of the wire;
* an **adversary** sub-interface (`signalAdv{In,Out}Iface`) for
  corruption / leak ports.

These are combined by `Interface.sum` into one input interface and
one output interface per party, packaged as a `PortBoundary`. The
two-party Signal boundary `Δ_signal` is the tensor of Alice's and
Bob's boundaries.

The choice of *which* messages live on each port reflects the
operational reading at the protocol level: the application emits
plaintexts under a chosen recipient; the network carries opaque
ciphertexts plus associated data; the adversary may request a
leak of the current session state.
-/

namespace Interaction
namespace UC
namespace Examples
namespace Signal

open Interaction.UC

/-! ### Application sub-interface

An application instance feeds the functionality with two kinds of
commands and consumes one kind of event:

* `AppCmd.send`  – ask the functionality to encrypt `msg` for `peer`;
* `AppCmd.init`  – ask the functionality to set up a fresh session
  with `peer`;
* `AppEvt.delivered` – the functionality returns a decrypted
  `(sender, plaintext)` pair to the application.
-/

/-- Application-side command ports (application → functionality). -/
inductive AppCmd where
  | send
  | init
  deriving DecidableEq, Repr, Inhabited

/-- Application-side event ports (functionality → application). -/
inductive AppEvt where
  | delivered
  deriving DecidableEq, Repr, Inhabited

/-- Application-input interface: messages the application sends to the
functionality. -/
def signalAppInIface : Interface where
  A := AppCmd
  B := fun
    | .send => Identity × Plaintext
    | .init => Identity

/-- Application-output interface: events the functionality returns to
the application. -/
def signalAppOutIface : Interface where
  A := AppEvt
  B := fun
    | .delivered => Identity × Plaintext

/-! ### Network sub-interface

The wire carries ciphertexts in both directions. Inbound packets are
indistinguishable from each other at the boundary level (the
functionality has to decrypt to learn the sender); outbound packets
are tagged with their intended recipient so the routing layer can
deliver them.
-/

/-- Network-input port (network → functionality): a single port
carrying an inbound ciphertext together with its associated data. -/
inductive NetIn where
  | recv
  deriving DecidableEq, Repr, Inhabited

/-- Network-output port (functionality → network): a single port
carrying an outbound ciphertext, its associated data, and the
intended recipient. -/
inductive NetOut where
  | send
  deriving DecidableEq, Repr, Inhabited

/-- Network-input interface. -/
def signalNetInIface : Interface where
  A := NetIn
  B := fun | .recv => Ciphertext × ADData

/-- Network-output interface. -/
def signalNetOutIface : Interface where
  A := NetOut
  B := fun | .send => Identity × Ciphertext × ADData

/-! ### Adversary sub-interface

Phase 0 exposes a minimal corruption surface: the adversary can ask
for the current session state, and the functionality may answer with
a leaked snapshot. Richer corruption modes (compromise of long-term
keys, deletion of forward-secret material, scheduling control) belong
to later phases and depend on the planned `CorruptionPolicy`
infrastructure.
-/

/-- Adversary-input port: the adversary requests a state leak. -/
inductive AdvIn where
  | corrupt
  deriving DecidableEq, Repr, Inhabited

/-- Adversary-output port: the functionality returns leaked state. -/
inductive AdvOut where
  | leakState
  deriving DecidableEq, Repr, Inhabited

/-- Adversary-input interface. -/
def signalAdvInIface : Interface where
  A := AdvIn
  B := fun | .corrupt => Unit

/-- Adversary-output interface. -/
def signalAdvOutIface : Interface where
  A := AdvOut
  B := fun | .leakState => SessionState

/-! ### Per-party boundaries

The `In` interface of one party is the disjoint sum of the
application-input, network-input, and adversary-input interfaces.
Likewise for `Out`. The two-party Signal boundary `Δ_signal` is the
tensor of Alice's and Bob's boundaries, which by `PortBoundary.tensor`
sums inputs and sums outputs side by side.
-/

/-- Combined input interface for one Signal party. -/
def signalInIface : Interface :=
  Interface.sum signalAppInIface (Interface.sum signalNetInIface signalAdvInIface)

/-- Combined output interface for one Signal party. -/
def signalOutIface : Interface :=
  Interface.sum signalAppOutIface (Interface.sum signalNetOutIface signalAdvOutIface)

/-- The boundary exposed by one Signal party (used uniformly for
Alice and Bob; per-party identification happens via the `Party`
parameter on the functionality). -/
def Δ_party : PortBoundary where
  In := signalInIface
  Out := signalOutIface

/-- Alice's boundary in the two-party Signal setting. -/
abbrev Δ_alice : PortBoundary := Δ_party

/-- Bob's boundary in the two-party Signal setting. -/
abbrev Δ_bob : PortBoundary := Δ_party

/-- The full two-party Signal boundary. -/
abbrev Δ_signal : PortBoundary := Δ_alice ⊗ᵇ Δ_bob

end Signal
end Examples
end UC
end Interaction

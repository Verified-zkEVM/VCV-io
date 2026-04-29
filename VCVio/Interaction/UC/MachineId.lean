/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.UC.OpenProcess

/-!
# Machine identity for UC composition

This file introduces `MachineId Sid Pid`, the `(sid, pid)` machine identity
used to address protocol participants in CJSV22-style universal composition
(Canetti, Jain, Swanberg, Varia, *Universally Composable End-to-End Secure
Messaging*, CRYPTO 2022). A machine is identified by a session identifier
`sid : Sid` and a party identifier `pid : Pid`. Within a single instantiated
session, party identifiers distinguish participants; across sessions, the
session identifier scopes who is allowed to talk to whom.

The framework's `OpenProcess Party Δ` is generic in its participant type
`Party`. Specializing `Party := MachineId Sid Pid` recovers the CJSV22 surface
where every protocol input and output is keyed by a `(sid, pid)` pair. The
abbreviation `MachineProcess Sid Pid Δ` names that specialization.

`MachineId` is intentionally additive: nothing in the existing UC layer
mentions it, and protocols that already use a flat `Party` continue to work
unchanged. New work that needs session-aware identity (forward security,
post-compromise security, multi-session composition) instantiates
`Party := MachineId Sid Pid` and uses the helpers below.

## Per-process access control and subroutine respecting

This file also introduces the access-control vocabulary required by the
CJSV22 *subroutine respecting* condition:

* **`HasAccessControl P`.** A typeclass over `OpenProcess Party Δ`
  carrying `allowed : Interface.RoutedPacket Δ.In Party → Bool`. The
  default-open instance `HasAccessControl.allowAll` is provided for
  protocols whose security is not sensitive to per-machine input
  filtering.
* **`MachineProcess.allowSameSession owner P`.** The canonical CJSV22
  filter on a `MachineProcess`: admit a routed packet iff its sender
  shares a session with `owner` (per `MachineId.sameSession`).
* **`MachineProcess.SubroutineRespectingAt sid P`.** A `Prop`-valued
  property saying every reachable step's decoration only attributes
  controllers in session `sid`. Built recursively over `Spec.Decoration`
  via `OpenNodeProfile.SessionCoherentAtMove` and
  `DecorationSessionCoherentAt`.

These three pieces are *additive* on top of the existing `OpenProcess`
surface: no existing construction site is touched, and the predicate
`SubroutineRespectingAt` reads off the controller annotations already
carried by `OpenNodeContext`.

## Deferred follow-up

The runtime integration that consults `HasAccessControl` from
`BoundaryAction.inputDecode` is deliberately deferred to the
corruption layer, which already needs to touch the boundary surface
for `EnvAction` dispatch. Until that integration lands,
`HasAccessControl` is a *declarative* contract that downstream
constructions thread by hand: the typeclass exposes the per-process
`allowed` predicate, but no construction in this file enforces it
against the runtime. Consumers that need the contract enforced should
filter incoming routed packets explicitly through `allowed` at the
appropriate boundary surface.
-/

universe u v w w'

namespace Interaction
namespace UC

/--
`MachineId Sid Pid` is the standard `(sid, pid)` machine identity from
CJSV22's universal composition with global subroutines.

Two machines are equal iff both their session identifier and party identifier
agree. Decidable equality is derived from decidable equality on `Sid` and
`Pid`.

The session identifier `Sid` is left abstract so users can pick the structure
that fits their composition style: a flat `Nat` or `String` for single-level
sessions, or a `List String` / prefix tree when nested subsessions need to
be addressed by hierarchical paths (the standard CJSV22 idiom for spawned
subprotocols).
-/
structure MachineId (Sid : Type u) (Pid : Type u) where
  sid : Sid
  pid : Pid
deriving DecidableEq

namespace MachineId

variable {Sid Pid : Type u}

theorem ext_iff {m₁ m₂ : MachineId Sid Pid} :
    m₁ = m₂ ↔ m₁.sid = m₂.sid ∧ m₁.pid = m₂.pid := by
  cases m₁; cases m₂; simp

@[ext]
theorem ext {m₁ m₂ : MachineId Sid Pid}
    (hsid : m₁.sid = m₂.sid) (hpid : m₁.pid = m₂.pid) : m₁ = m₂ := by
  rw [ext_iff]; exact ⟨hsid, hpid⟩

/--
Two machines belong to the same protocol session iff their session identifiers
agree.

This is the syntactic ingredient of CJSV22's "subroutine respecting" check:
within a subroutine respecting protocol, a machine routes inbound and outbound
messages only between machines sharing its `sid`.
-/
def sameSession [DecidableEq Sid] (m₁ m₂ : MachineId Sid Pid) : Bool :=
  decide (m₁.sid = m₂.sid)

@[simp]
theorem sameSession_self [DecidableEq Sid] (m : MachineId Sid Pid) :
    m.sameSession m = true := by
  simp [sameSession]

theorem sameSession_iff [DecidableEq Sid] (m₁ m₂ : MachineId Sid Pid) :
    m₁.sameSession m₂ = true ↔ m₁.sid = m₂.sid := by
  simp [sameSession]

theorem sameSession_comm [DecidableEq Sid] (m₁ m₂ : MachineId Sid Pid) :
    m₁.sameSession m₂ = m₂.sameSession m₁ := by
  simp [sameSession, eq_comm]

theorem sameSession_trans [DecidableEq Sid] {m₁ m₂ m₃ : MachineId Sid Pid}
    (h₁₂ : m₁.sameSession m₂ = true) (h₂₃ : m₂.sameSession m₃ = true) :
    m₁.sameSession m₃ = true := by
  rw [sameSession_iff] at h₁₂ h₂₃ ⊢
  exact h₁₂.trans h₂₃

end MachineId

/--
`MachineProcess Sid Pid Δ` is the specialization of `OpenProcess` to processes
whose participants are identified by `(sid, pid)` machine identities.

This is the canonical type for protocols written in the CJSV22 idiom: every
input and output packet is keyed by a `MachineId Sid Pid`, and session-scoped
composition operates uniformly over this type.

Existing examples that use a flat `Party` are unaffected; only protocols that
need session-aware identity instantiate this abbreviation.
-/
abbrev MachineProcess (Sid Pid : Type u) (m : Type w → Type w') (Δ : PortBoundary) :=
  OpenProcess.{u, v, w, w'} m (MachineId Sid Pid) Δ

/-! ## Per-process access control -/

/--
`HasAccessControl P` is the per-process predicate deciding which routed
inbound packets are admissible to the open process `P`.

For an open process `P : OpenProcess Party Δ`, an instance supplies
`allowed : Interface.RoutedPacket Δ.In Party → Bool`. The runtime layer
consults this typeclass when delivering inbound packets: a packet is
forwarded to `P` only when `allowed rp = true`.

The default for new instances is **allow everything** (`HasAccessControl.allowAll`).
Protocols that need sender-aware filtering provide a more restrictive
instance. The canonical CJSV22-style filter
(`MachineProcess.allowSameSession`) admits a packet iff its sender shares a
session with the process owner, recovering the access-control fragment of
the subroutine respecting condition (CJSV22 §2.3).

The runtime integration into `BoundaryAction.inputDecode` is deliberately
**not** wired up in this slice: the typeclass exists as a forward-compatible
vocabulary that downstream layers (notably the F2 corruption work) consume.
Until that integration lands, `HasAccessControl` is a *declarative* contract
that downstream constructions must thread by hand.
-/
class HasAccessControl
    {Party : Type u} {m : Type w → Type w'} {Δ : PortBoundary}
    (P : OpenProcess.{u, v, w, w'} m Party Δ) where
  allowed : Interface.RoutedPacket Δ.In Party → Bool

namespace HasAccessControl

variable {Party : Type u} {m : Type w → Type w'} {Δ : PortBoundary}

/--
The trivial **allow-all** access control: every routed packet is admissible.

Useful for protocols whose security does not depend on per-machine input
filtering, and as the canonical baseline against which more restrictive
instances are compared.
-/
@[reducible]
def allowAll (P : OpenProcess.{u, v, w, w'} m Party Δ) : HasAccessControl P where
  allowed _ := true

@[simp]
theorem allowed_allowAll
    (P : OpenProcess.{u, v, w, w'} m Party Δ)
    (rp : Interface.RoutedPacket Δ.In Party) :
    (HasAccessControl.allowAll P).allowed rp = true := rfl

end HasAccessControl

/--
The canonical CJSV22 same-session access control on a `MachineProcess`.

`MachineProcess.allowSameSession owner P` admits a routed packet iff its
sender shares a session with `owner` (per `MachineId.sameSession`).

This is the access-control fragment of the **subroutine respecting**
condition (CJSV22 §2.3): a machine `(s, p)` only accepts inputs from
senders whose session identifier is also `s`. Combined with a sender-aware
emit (delivered by F2), this recovers the full structural same-session
discipline.
-/
@[reducible]
def MachineProcess.allowSameSession
    {Sid Pid : Type u} {m : Type w → Type w'} {Δ : PortBoundary} [DecidableEq Sid]
    (owner : MachineId Sid Pid)
    (P : MachineProcess.{u, v, w, w'} Sid Pid m Δ) : HasAccessControl P where
  allowed rp := rp.sender.sameSession owner

@[simp]
theorem MachineProcess.allowed_allowSameSession
    {Sid Pid : Type u} {m : Type w → Type w'} {Δ : PortBoundary} [DecidableEq Sid]
    (owner : MachineId Sid Pid)
    (P : MachineProcess.{u, v, w, w'} Sid Pid m Δ)
    (rp : Interface.RoutedPacket Δ.In (MachineId Sid Pid)) :
    (MachineProcess.allowSameSession owner P).allowed rp =
      rp.sender.sameSession owner := rfl

/-! ## Subroutine respecting predicate -/

/--
A node semantics is **session-coherent at** `sid` for a chosen move `x`
iff every controller listed by the node for that move resides in
session `sid`.

This is the per-move check used by `DecorationSessionCoherentAt`: at the
node where `x` is chosen, every machine credited as a controller of `x`
must share the protocol's session identifier.
-/
def OpenNodeProfile.SessionCoherentAtMove
    {Sid Pid : Type u} {Δ : PortBoundary} {X : Type w}
    (sid : Sid) (ons : OpenNodeProfile (MachineId Sid Pid) Δ X)
    (x : X) : Prop :=
  ∀ m ∈ ons.controllers x, m.sid = sid

/--
A spec decoration is **session-coherent at** `sid` along a chosen
transcript iff every visited node attributes only controllers in
session `sid`.

This is the recursive companion to
`OpenNodeProfile.SessionCoherentAtMove`, modeled directly on
`IsSilentDecoration`: the predicate walks the same transcript path
through the decoration tree and accumulates the per-node coherence
checks.
-/
def DecorationSessionCoherentAt
    {Sid Pid : Type u} {Δ : PortBoundary} (sid : Sid) :
    {spec : Interaction.Spec.{w}} →
    Interaction.Spec.Decoration
      (OpenNodeContext.{u, w} (MachineId Sid Pid) Δ) spec →
    spec.Transcript → Prop
  | .done, _, _ => True
  | .node _ _, ⟨ons, drest⟩, ⟨x, tr⟩ =>
      ons.SessionCoherentAtMove sid x ∧
      DecorationSessionCoherentAt sid (drest x) tr

/--
A `MachineProcess` is **subroutine respecting at** `sid` iff every step
from every reachable state, along every transcript path, only attributes
controllers in session `sid`.

This is the **controller-side** fragment of CJSV22's subroutine
respecting condition. The sender-side fragment (every emitted /
accepted `RoutedPacket` has sender in session `sid`) lives at the
`BoundaryAction` integration layer and is enforced by future
`HasAccessControl` instances installed via
`MachineProcess.allowSameSession`.
-/
def MachineProcess.SubroutineRespectingAt
    {Sid Pid : Type u} {m : Type w → Type w'} {Δ : PortBoundary}
    (sid : Sid) (P : MachineProcess.{u, v, w, w'} Sid Pid m Δ) : Prop :=
  ∀ (s : P.Proc) (tr : (P.step s).spec.Transcript),
    DecorationSessionCoherentAt sid (P.step s).semantics tr

@[simp]
theorem DecorationSessionCoherentAt_done
    {Sid Pid : Type u} {Δ : PortBoundary} (sid : Sid)
    (d : Interaction.Spec.Decoration
      (OpenNodeContext.{u, w} (MachineId Sid Pid) Δ) .done)
    (tr : (Interaction.Spec.done : Interaction.Spec.{w}).Transcript) :
    DecorationSessionCoherentAt sid d tr := by
  trivial

@[simp]
theorem DecorationSessionCoherentAt_node
    {Sid Pid : Type u} {Δ : PortBoundary} (sid : Sid)
    {Moves : Type w} {residual : Moves → Interaction.Spec.{w}}
    (d : Interaction.Spec.Decoration
      (OpenNodeContext.{u, w} (MachineId Sid Pid) Δ)
      (.node Moves residual))
    (x : Moves)
    (tr : (residual x).Transcript) :
    DecorationSessionCoherentAt sid d ⟨x, tr⟩ ↔
      d.1.SessionCoherentAtMove sid x ∧
      DecorationSessionCoherentAt sid (d.2 x) tr := by
  rcases d with ⟨ons, drest⟩
  rfl

end UC
end Interaction

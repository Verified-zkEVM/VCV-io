/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
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

## Status of related layers (deferred follow-ups)

The full CJSV22 access-control story requires three additional pieces that are
deliberately *not* introduced here, because each one carries a non-trivial
cross-cutting design choice and they ship together as a coherent unit:

* **`Interface.Packet.sender : MachineId`.** A packet currently carries only a
  recipient port. Adding a sender field is invasive (every existing packet
  construction site needs updating). Without it, the framework cannot tell
  which machine sent an inbound packet, so any access-control predicate has
  nothing concrete to inspect.
* **`HasAccessControl` typeclass.** Per-process predicate
  `allowed : MachineId → Packet → Bool` consulted by
  `BoundaryAction.inputDecode` to drop ill-addressed packets. Depends on
  `Packet.sender` to be expressible.
* **`subroutineRespecting : MachineProcess Sid Pid Δ → Prop`.** A decidable,
  structural predicate that recovers what an explicit scope policy would
  otherwise enforce: a machine `(s, p)` only emits to and accepts packets
  tagged with session `s`. Defining it cleanly requires `Packet.sender` so
  the predicate has something concrete to read off the boundary action.

These three are tracked together as the next slice of the F1 plan; see
`Notes/vcvio-signal-uc-foundation-cjsv22.md` §6.10.1 and the F1 phase
description for the proposed naming and the broader composition story.
-/

universe u v w

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
abbrev MachineProcess (Sid Pid : Type u) (Δ : PortBoundary) :=
  OpenProcess.{u, v, w} (MachineId Sid Pid) Δ

end UC
end Interaction

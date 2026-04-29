/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.Interaction.Multiparty.ObservationProfile

/-!
# Sketch: aspect-indexed observation kernels for sealed-sender messaging

A Signal-flavored single-step protocol used to exercise
`Multiparty.Observation` and the `ObservationProfile` algebra.

Three real parties (Sender, Server, Recipient) plus a passive Network observer
exchange one structured packet. Different parties — and different
**corruptions** of those parties — observe **different projections** of the
same underlying packet. The honest Server is "honest-but-curious" and sees
routing + ciphertext but not the MAC tag; the passive Network observer sees
only the envelope, the ciphertext length, and the timestamp; corruption
modes upgrade or downgrade specific parties' observation kernels.

The point of this sketch is not to model a complete protocol. It is to
demonstrate that:

* per-party observation kernels are naturally **`Observation`-valued** functions
  of a corruption mode, not `ViewMode`-valued ones;
* refinement (`≤` on `Observation` via the `Preorder` instance) is the natural
  "this corruption reveals no more than that one" relation;
* coalition observations (`⊔` on `Observation` via the `Max` instance) are the
  natural Σ-product join in the information lattice;
* the lifting back into the `ViewProfile` / `Profile.Strategy` pipeline goes
  through `ObservationProfile.toViewProfile`, with one bridge step per node.

Sealed-sender (the Server's view of `envFrom` is *removed*) and a MAC-aware
network adversary (the Network's view of `macTag` and `tagLen` is *added*)
are concrete corruption directions in this sketch.

Throughout, we use Mathlib's order notation (`⊤`, `⊥`, `≤`, `⊔`) rather than
the named `Observation.top` / `Observation.bot` / `Observation.Refines` /
`Observation.combine` operations. Both APIs are equivalent definitionally;
the notation buys readability and lets profile-level facts come through
`Pi`-instance lifting.
-/

universe u

namespace Examples
namespace SealedSender

open Interaction Multiparty

/-! ## Packet, parties, and modes -/

/-- An idealized end-to-end packet for one send. -/
structure Packet where
  /-- Sender id (numeric placeholder). -/
  envFrom : Nat
  /-- Recipient id. -/
  envTo : Nat
  /-- Payload (numeric placeholder). -/
  ciphertext : Nat
  /-- Length of the ciphertext. -/
  ctLen : Nat
  timestamp : Nat
  macTag : Nat
  tagLen : Nat

/-- The four parties in the sketch: real Sender / Server / Recipient and a
passive Network observer. -/
inductive Party
  | Sender
  | Server
  | Recipient
  | Net
  deriving DecidableEq

/-- A small space of corruption modes. -/
inductive Mode
  | clean
  | serverFull         -- Server fully corrupted: sees the entire packet
  | serverSealed       -- Sealed-sender: Server's `envFrom` is hidden
  | netMacAware        -- Network adversary additionally sees the MAC tag
  deriving DecidableEq

/-! ## Honest per-party observation views -/

/-- The honest Server's observation: routing + ciphertext + timestamp, no MAC. -/
structure ServerView where
  envFrom : Nat
  envTo : Nat
  ciphertext : Nat
  timestamp : Nat

/-- The honest passive Network observer: envelope + ciphertext length + timestamp. -/
structure NetView where
  envFrom : Nat
  envTo : Nat
  ctLen : Nat
  timestamp : Nat

/-- Sealed-sender's view of the Server: as `ServerView` but with `envFrom`
stripped. -/
structure ServerSealedView where
  envTo : Nat
  ciphertext : Nat
  timestamp : Nat

/-- The MAC-aware passive network observer: like `NetView` but also sees the
MAC tag and its length. -/
structure NetMacAwareView where
  envFrom : Nat
  envTo : Nat
  ctLen : Nat
  timestamp : Nat
  macTag : Nat
  tagLen : Nat

/-! ## Honest and corrupted observations -/

namespace Observations

/-- Honest Server projection. -/
def serverHonest : Observation Packet :=
  ⟨ServerView, fun p => ⟨p.envFrom, p.envTo, p.ciphertext, p.timestamp⟩⟩

/-- Sealed-sender Server projection: drops `envFrom`. -/
def serverSealed : Observation Packet :=
  ⟨ServerSealedView, fun p => ⟨p.envTo, p.ciphertext, p.timestamp⟩⟩

/-- Server fully corrupted: identity projection (top of the information
lattice). -/
def serverFull : Observation Packet := ⊤

/-- Honest passive Network observer: envelope + length + time. -/
def netHonest : Observation Packet :=
  ⟨NetView, fun p => ⟨p.envFrom, p.envTo, p.ctLen, p.timestamp⟩⟩

/-- MAC-aware network observer: adds `macTag` and `tagLen` to `netHonest`. -/
def netMacAware : Observation Packet :=
  ⟨NetMacAwareView,
    fun p => ⟨p.envFrom, p.envTo, p.ctLen, p.timestamp, p.macTag, p.tagLen⟩⟩

/-! ### Refinement facts on individual observations

Each fact is a single-line `⟨factor_map, fun _ => rfl⟩` proof, illustrating
how refinement reduces to giving a Σ-factorization between observation
types. -/

/-- Sealed-sender Server is no more revealing than honest Server: drop `envFrom`. -/
theorem serverSealed_le_serverHonest : serverSealed ≤ serverHonest :=
  ⟨fun v => ⟨v.envTo, v.ciphertext, v.timestamp⟩, fun _ => rfl⟩

/-- Honest Server is no more revealing than fully-corrupted Server: project
out the four observed fields. -/
theorem serverHonest_le_serverFull : serverHonest ≤ serverFull :=
  ⟨fun p => ⟨p.envFrom, p.envTo, p.ciphertext, p.timestamp⟩, fun _ => rfl⟩

/-- By transitivity, sealed-sender Server is no more revealing than the fully
corrupted Server. -/
theorem serverSealed_le_serverFull : serverSealed ≤ serverFull :=
  le_trans serverSealed_le_serverHonest serverHonest_le_serverFull

/-- Honest Network observer is no more revealing than the MAC-aware variant. -/
theorem netHonest_le_netMacAware : netHonest ≤ netMacAware :=
  ⟨fun v => ⟨v.envFrom, v.envTo, v.ctLen, v.timestamp⟩, fun _ => rfl⟩

end Observations

/-! ## Per-mode observation profiles -/

open Profile

/-- The corruption-mode-indexed observation: for each mode and party, the
observation kernel of that party in that mode.

* In every mode, `Sender` and `Recipient` see the full packet (their
  operational shapes — `.pick` and `.observe` respectively — would be
  recovered from a separate operational decoration; here we only record their
  *observation kernel*, which is the top of the information lattice `⊤`).
* `Server`'s kernel varies with the mode: honest, sealed, or fully corrupted.
* `Net`'s kernel varies between honest and MAC-aware. -/
def observationOf : Mode → Party → Observation Packet
  | _,                .Sender    => ⊤
  | _,                .Recipient => ⊤
  | .clean,           .Server    => Observations.serverHonest
  | .serverSealed,    .Server    => Observations.serverSealed
  | .serverFull,      .Server    => Observations.serverFull
  | .netMacAware,     .Server    => Observations.serverHonest
  | .clean,           .Net       => Observations.netHonest
  | .serverSealed,    .Net       => Observations.netHonest
  | .serverFull,      .Net       => Observations.netHonest
  | .netMacAware,     .Net       => Observations.netMacAware

/-- The observation profile attached to one node in a given corruption mode.

This is the *kernel-form* analogue of a `ViewProfile` per node. Plugging it
into `Profile.Strategy` requires `ObservationProfile.toViewProfile` to bridge
to the existing endpoint pipeline. -/
def observationProfile (m : Mode) : ObservationProfile Party Packet :=
  fun p => observationOf m p

/-- The induced view profile (each party's observation kernel becomes the
universal `.react` `ViewMode`). -/
def viewProfile (m : Mode) : ViewProfile Party Packet :=
  ObservationProfile.toViewProfile (observationProfile m)

/-! ## Refinement facts on profiles

These illustrate the payoff of working at the kernel level: monotonicity in
the corruption order is proved pointwise by the per-observation refinement
facts above, with no four-case `ViewMode` matching. The pointwise `≤` on
profiles comes from `Pi.preorder` and the per-party `Preorder (Observation
Packet)` instance — no manual `Refines` definition is needed. -/

/-- Sealed-sender mode is no more revealing than the clean mode (only `Server`
differs, and the sealed-sender Server kernel refines the honest Server
kernel). -/
theorem observationProfile_serverSealed_le_clean :
    observationProfile .serverSealed ≤ observationProfile .clean := by
  intro p
  cases p
  · exact le_refl _
  · exact Observations.serverSealed_le_serverHonest
  · exact le_refl _
  · exact le_refl _

/-- Clean mode is no more revealing than fully-corrupted-Server mode (only
`Server` differs, and the honest Server kernel refines the fully-corrupted
Server kernel). -/
theorem observationProfile_clean_le_serverFull :
    observationProfile .clean ≤ observationProfile .serverFull := by
  intro p
  cases p
  · exact le_refl _
  · exact Observations.serverHonest_le_serverFull
  · exact le_refl _
  · exact le_refl _

/-- Clean mode is no more revealing than the MAC-aware-network mode. -/
theorem observationProfile_clean_le_netMacAware :
    observationProfile .clean ≤ observationProfile .netMacAware := by
  intro p
  cases p
  · exact le_refl _
  · exact le_refl _
  · exact le_refl _
  · exact Observations.netHonest_le_netMacAware

/-! ## Coalition example

The `Server`-`Net` coalition's observation in the clean mode is the Σ-product
of `serverHonest` and `netHonest`. Both factors refine into it, automatically. -/

/-- The Server-plus-Net coalition kernel in the clean mode: a Σ-product of
the two honest kernels (the **join** in the information lattice). -/
def serverNetCoalitionClean : Observation Packet :=
  Observations.serverHonest ⊔ Observations.netHonest

example : Observations.serverHonest ≤ serverNetCoalitionClean :=
  Observation.refines_combine_left _ _

example : Observations.netHonest ≤ serverNetCoalitionClean :=
  Observation.refines_combine_right _ _

end SealedSender
end Examples

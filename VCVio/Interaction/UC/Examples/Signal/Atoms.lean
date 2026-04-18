/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.BitVec

/-!
# Signal protocol — atomic types

Concrete data types used throughout the Signal/Double-Ratchet
formalization. Everything here lives in `Type 0` so it is compatible
with the universe constraints imposed by `UC.processSemantics` and
`UC.processSemanticsOracle`.

Sizes for the keyed material follow the parameter choices in the
Signal Double-Ratchet specification (e.g., 256-bit AEAD keys, 256-bit
chain/root keys, 256-bit X25519 public/secret keys). They are kept as
opaque `BitVec n` placeholders at this stage; later phases will refine
specific atoms (the DH atoms in particular) into proper algebraic
group structures.

The `SessionState` record collects the per-party Double-Ratchet state
needed by the protocol functionality. Phase 0 only requires the field
*types* to be in place; later phases populate the corresponding
operational behavior.
-/

namespace Interaction
namespace UC
namespace Examples
namespace Signal

/-! ### Parties -/

/-- The two-party setting of the Signal protocol. -/
inductive Party where
  | alice
  | bob
  deriving DecidableEq, Repr, Inhabited

/-! ### Identifiers and keyed material

These are kept as concrete bit-string aliases at Phase 0. Later phases
may swap individual atoms for algebraic structures (e.g., `DHPub` for
an element of a prime-order group obtained from a `Module F G`
instance), without affecting the rest of the development.
-/

/-- A long-term party identifier (e.g., a hashed identity public key). -/
abbrev Identity : Type := BitVec 256

/-- A unique session identifier shared by Alice and Bob. -/
abbrev SessionId : Type := BitVec 128

/-- A 256-bit Double-Ratchet root key. -/
abbrev RootKey : Type := BitVec 256

/-- A 256-bit chain key produced by the symmetric-ratchet KDF chain. -/
abbrev ChainKey : Type := BitVec 256

/-- A 256-bit message key derived from a chain key, fed into AEAD. -/
abbrev MessageKey : Type := BitVec 256

/-- The message index within a chain. -/
abbrev MessageIdx : Type := Nat

/-- An X25519 public key (placeholder; later phases may refine to a
group element). -/
abbrev DHPub : Type := BitVec 256

/-- An X25519 secret key (placeholder). -/
abbrev DHSec : Type := BitVec 256

/-- Associated data attached to AEAD ciphertexts. -/
abbrev ADData : Type := List (BitVec 8)

/-- Application-level plaintexts. -/
abbrev Plaintext : Type := List (BitVec 8)

/-- AEAD ciphertexts emitted on the network boundary. -/
abbrev Ciphertext : Type := List (BitVec 8)

/-! ### Per-party session state

The fields cover the symmetric-ratchet bookkeeping (root key, sending
and receiving chain keys, send/receive message counters), the
asymmetric ratchet state (the locally held DH secret and the most
recent peer DH public key), and a protocol-local corruption flag.
All cryptographic fields are `Option`-typed so that an uninitialized
session is representable; initialization occurs when the application
boundary receives a session-setup command.

The `corrupted` flag is local protocol state: it records whether the
adversary has previously asked for a leak through the `AdvIn.corrupt`
port. A framework-level `CorruptionPolicy` (which would centralize
the same information across multiple functionalities and across
composed sub-protocols) is deferred to a later phase; until then,
each functionality tracks its own corruption status in its residual
state.
-/

/-- The Double-Ratchet state held by a single party. -/
structure SessionState where
  /-- The session identifier, set on initialization. -/
  sessionId : Option SessionId := none
  /-- The current 256-bit root key. -/
  rootKey : Option RootKey := none
  /-- The current sending-chain key. -/
  sendingChain : Option ChainKey := none
  /-- The current receiving-chain key. -/
  receivingChain : Option ChainKey := none
  /-- Index of the next outbound message in the current sending chain. -/
  sendIdx : MessageIdx := 0
  /-- Index of the next inbound message in the current receiving chain. -/
  recvIdx : MessageIdx := 0
  /-- The DH secret currently held by this party. -/
  ourDHSec : Option DHSec := none
  /-- The peer's most recently advertised DH public key. -/
  peerDHPub : Option DHPub := none
  /-- Whether this party has been corrupted by the adversary (a
  state-leak request has been observed). -/
  corrupted : Bool := false
  deriving Inhabited

end Signal
end Examples
end UC
end Interaction

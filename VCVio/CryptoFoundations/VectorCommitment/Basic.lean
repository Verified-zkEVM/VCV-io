/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import VCVio.EvalDist.TVDist

/-!
# Vector Commitments

This file defines `VectorCommitment`, a monad-generic abstraction of a (positional) vector
commitment: a primitive that commits to a whole vector of values `data : ι → α` with a single short
`Commit`, and later lets the committer *open* the value at any individual position `i : ι` with a
short `Opening` that the verifier can check against the commitment alone.

This is the intermediate layer that sits between a concrete construction — such as the inductive
Merkle tree in `VCVio.CryptoFoundations.MerkleTree.Inductive.Defs` (whose vector-commitment
instance is in `VCVio.CryptoFoundations.MerkleTree.Inductive.VectorCommitment`) — and consumers that
only need the positional commit/open/verify interface, such as the Kilian transformation
(`VCVio.CryptoFoundations.Kilian`).

## Type Parameters

- `m`: the monad in which committing and opening run (e.g. `ProbComp`, or a hash-oracle monad).
- `ι`: positions / indices into the committed vector.
- `α`: the value stored at each position.
- `Commit`: the public commitment, sent to the verifier.
- `State`: the committer's private state, retained after committing and used to open positions.
- `Opening`: the per-position opening / proof checked by `verifyOpen`.

Unlike a single-message `CommitmentScheme`, a vector commitment exposes *positional* opening: the
opener reveals only the positions a verifier asks about, paying a per-position `Opening` rather than
a decommitment to the entire vector. Succinctness — `Commit` and `Opening` being much smaller than
the vector — is what makes the primitive interesting, though that is a property of a particular
instance rather than part of this interface.

We also provide `BatchOpeningVectorCommitment`, a variant whose opening and verification work on a
*list* of positions at once with a single `BatchOpening`. The two notions are interconvertible:
`BatchOpeningVectorCommitment.toVectorCommitment` opens singleton batches, and
`VectorCommitment.toBatchOpening` assembles a batch opening from the individual openings. A genuine
batch scheme (e.g. one sharing authentication-path hashes across positions) can be more succinct
than the round-trip through single openings, so the conversions are bridges, not isomorphisms.

## Probability assumptions

As with `ChallengeVerifyProtocol`, probability reasoning is expressed through the standard
`MonadLiftT m SetM` lift introduced in the `EvalDist` layer, so `support` is available for the
monadic `commit` / `openAt` fields.
-/

/-- A vector commitment whose `commit` and `openAt` operations run in the monad `m`.

`commit data` commits to the whole vector `data : ι → α`, producing a public `Commit` together with
private `State`. `decode st i` reads back the committed value at position `i` from that state (the
committer always knows what it committed). `openAt st i` produces an `Opening` for position `i`, and
`verifyOpen c i v op` deterministically checks that `op` certifies value `v` at position `i` under
commitment `c`.

The monad is left abstract so an instance may be purely functional (Merkle trees with an explicit
hash function), randomized (`ProbComp`), or oracle-querying. -/
structure VectorCommitment
    (m : Type → Type) (ι α Commit State Opening : Type) where
  /-- Commit to the whole vector `data`, returning a public commitment and private opener state. -/
  commit (data : ι → α) : m (Commit × State)
  /-- Read back the committed value at position `i` from the opener's state. -/
  decode (st : State) (i : ι) : α
  /-- Produce an opening for the value at position `i`. -/
  openAt (st : State) (i : ι) : m Opening
  /-- Deterministically check that `op` certifies value `v` at position `i` under commitment `c`. -/
  verifyOpen (c : Commit) (i : ι) (v : α) (op : Opening) : Bool

namespace VectorCommitment

variable {m : Type → Type} [Monad m]
  [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
  {ι α Commit State Opening : Type}

/-- A vector commitment is **perfectly correct** if, for every vector and position, any honestly
produced commitment/state opens at that position to the committed value and passes verification. -/
def PerfectlyCorrect (vc : VectorCommitment m ι α Commit State Opening) : Prop :=
  ∀ (data : ι → α) (i : ι) (c : Commit) (st : State),
    (c, st) ∈ support (vc.commit data) →
      ∀ op ∈ support (vc.openAt st i), vc.verifyOpen c i (vc.decode st i) op = true

/-- A vector commitment is **position binding** if no commitment can be opened at a single position
to two different values: any two openings that both verify at the same position and commitment must
certify the same value. This is the property that makes the commitment useful for soundness in
consumers like the Kilian transformation. -/
def PositionBinding (vc : VectorCommitment m ι α Commit State Opening) : Prop :=
  ∀ (c : Commit) (i : ι) (v₁ : α) (op₁ : Opening) (v₂ : α) (op₂ : Opening),
    vc.verifyOpen c i v₁ op₁ = true → vc.verifyOpen c i v₂ op₂ = true → v₁ = v₂

end VectorCommitment

/-- A **batch-opening** vector commitment: like `VectorCommitment`, but a single `BatchOpening`
covers a whole *list* of positions, and verification checks a list of position/value `claims` at
once.

This is the natural interface for constructions that amortize work across positions — for instance a
Merkle proof that shares interior sibling hashes between several opened leaves — where a combined
opening can be smaller than the concatenation of per-position openings. -/
structure BatchOpeningVectorCommitment
    (m : Type → Type) (ι α Commit State BatchOpening : Type) where
  /-- Commit to the whole vector `data`, returning a public commitment and private opener state. -/
  commit (data : ι → α) : m (Commit × State)
  /-- Read back the committed value at position `i` from the opener's state. -/
  decode (st : State) (i : ι) : α
  /-- Produce a single opening covering all positions in `is`. -/
  openBatch (st : State) (is : List ι) : m BatchOpening
  /-- Check that `op` certifies every `(position, value)` pair in `claims` under commitment `c`. -/
  verifyBatch (c : Commit) (claims : List (ι × α)) (op : BatchOpening) : Bool

namespace VectorCommitment

variable {m : Type → Type} [Monad m] {ι α Commit State Opening : Type}

/-- Turn a single-position `VectorCommitment` into a `BatchOpeningVectorCommitment` by opening each
requested position individually and bundling the results. A batch opening is the list of
`(position, value, opening)` triples; `verifyBatch` checks that each claim is matched by such a
triple whose opening verifies. -/
def toBatchOpening [DecidableEq ι] [DecidableEq α]
    (vc : VectorCommitment m ι α Commit State Opening) :
    BatchOpeningVectorCommitment m ι α Commit State (List (ι × α × Opening)) where
  commit := vc.commit
  decode := vc.decode
  openBatch st is := is.mapM fun i => do
    let op ← vc.openAt st i
    return (i, vc.decode st i, op)
  verifyBatch c claims op :=
    claims.all fun iv =>
      match op.find? (fun e => decide (e.1 = iv.1)) with
      | some e => decide (e.2.1 = iv.2) && vc.verifyOpen c iv.1 iv.2 e.2.2
      | none => false

end VectorCommitment

namespace BatchOpeningVectorCommitment

variable {m : Type → Type} {ι α Commit State BatchOpening : Type}

/-- Turn a `BatchOpeningVectorCommitment` into a single-position `VectorCommitment` by opening and
verifying singleton batches. The opening type is the underlying `BatchOpening`. -/
def toVectorCommitment (bovc : BatchOpeningVectorCommitment m ι α Commit State BatchOpening) :
    VectorCommitment m ι α Commit State BatchOpening where
  commit := bovc.commit
  decode := bovc.decode
  openAt st i := bovc.openBatch st [i]
  verifyOpen c i v op := bovc.verifyBatch c [(i, v)] op

end BatchOpeningVectorCommitment

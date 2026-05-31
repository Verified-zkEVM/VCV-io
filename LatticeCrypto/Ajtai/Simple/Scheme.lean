/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Params
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Simple Ajtai Commitment Scheme

Definitions for the simple non-hiding Ajtai commitment over a bundled negacyclic ring.
This definition is simply matrix multiplication `A *ᵥ s`.
-/

open OracleComp
open CommitmentScheme

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the simple Ajtai commitment. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows cols : Nat) :=
  PolyMatrix ring.Poly rows cols

/-- Messages for the simple Ajtai commitment. -/
abbrev Message (ring : NegacyclicRing Coeff) (cols : Nat) :=
  PolyVec ring.Poly cols

/-- Commitments for the simple Ajtai commitment. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  PolyVec ring.Poly rows

/-- Deterministically commit by multiplying the public matrix by the message vector. -/
def commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    (A : PublicParams ring rows cols) (s : Message ring cols) : Commitment ring rows :=
  A *ᵥ s

/-- The simple Ajtai commitment has no auxiliary opening data. -/
abbrev Opening := Unit

/-- Verify a simple Ajtai opening by checking the matrix product. -/
def verify (ring : NegacyclicRing Coeff) {rows cols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows cols) (s : Message ring cols)
    (c : Commitment ring rows) (_opening : Opening) : Bool :=
  commit ring A s == c

/-- The simple Ajtai commitment instantiated as `CommitmentScheme`.

An opening is valid only when the message is accepted by the short-vector predicate
`isShort` (as required for the binding reduction to Module-SIS): verification checks
both shortness of the message and the matrix product. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows cols : Nat)
    (isShort : Message ring cols → Bool)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      Opening where
  setup := $ᵗ PublicParams ring rows cols
  commit A s := pure (commit ring A s, ())
  verify A s c opening := isShort s && verify ring A s c opening

end Simple
end Ajtai
end LatticeCrypto

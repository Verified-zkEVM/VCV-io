/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Gadget
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Simple Ajtai Commitment

The simple Ajtai commitment over a bundled negacyclic ring.  Public parameters
are a uniformly sampled matrix `A`; committing to a vector `s` returns `A * s`
and opens by revealing `s`. Non-hiding, but binding under Module-SIS.
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Simple

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for the simple Ajtai commitment. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows cols : Nat) :=
  RqMatrix ring rows cols

/-- Messages/openings for the simple Ajtai commitment. -/
abbrev Message (ring : NegacyclicRing Coeff) (cols : Nat) :=
  RqVec ring cols

/-- Commitments for the simple Ajtai commitment. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  RqVec ring rows

/-- Deterministically commit by multiplying the public matrix by the message vector. -/
def commit (ring : NegacyclicRing Coeff) {rows cols : Nat}
    (A : PublicParams ring rows cols) (s : Message ring cols) : Commitment ring rows :=
  matVecMul ring A s

/-- The simple Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows cols : Nat)
    [SampleableType (PublicParams ring rows cols)]
    [DecidableEq (Message ring cols)] [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows cols)
      (Message ring cols)
      (Commitment ring rows)
      (Message ring cols) where
  setup := $ᵗ PublicParams ring rows cols
  commit A s := pure (commit ring A s, s)
  verify A s c opening := decide (opening = s ∧ commit ring A opening = c)

end Simple
end Ajtai
end LatticeCrypto

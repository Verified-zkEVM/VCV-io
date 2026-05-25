/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Gadget
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Hiding Ajtai Commitment With Blinding

The standard blinded Ajtai commitment. Public parameters are a uniformly
sampled matrix `A`; committing to a message vector `m` samples a blinding vector
`r` and outputs `A * r + m`.

The file also provides a gadget-embedded variant `gadgetCommitmentScheme`, which
uses `A * r + G * m` for the base-`base` gadget matrix `G`.
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Hiding

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for blinded Ajtai commitments. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows blindCols : Nat) :=
  RqMatrix ring rows blindCols

/-- Blinded Ajtai commitments live in the row space of the public matrix. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  RqVec ring rows

/-- Openings are the sampled blinding vectors. -/
abbrev Opening (ring : NegacyclicRing Coeff) (blindCols : Nat) :=
  RqVec ring blindCols

/-- Commit as `A * r + m`, where `r` is the opening. -/
def commitWithOpening (ring : NegacyclicRing Coeff) {rows blindCols : Nat}
    (A : PublicParams ring rows blindCols) (m : RqVec ring rows)
    (r : Opening ring blindCols) : Commitment ring rows :=
  vecAdd ring (matVecMul ring A r) m

/-- The blinded Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows blindCols)
      (RqVec ring rows)
      (Commitment ring rows)
      (Opening ring blindCols) where
  setup := $ᵗ PublicParams ring rows blindCols
  commit A m := do
    let r ← $ᵗ Opening ring blindCols
    pure (commitWithOpening ring A m r, r)
  verify A m c r := decide (commitWithOpening ring A m r = c)

/-- Commit as `A * r + G * m`, where `G` is a gadget matrix. -/
def gadgetCommitWithOpening (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows messageDigits blindCols : Nat}
    (A : PublicParams ring rows blindCols) (m : RqVec ring (rows * messageDigits))
    (r : Opening ring blindCols) : Commitment ring rows :=
  vecAdd ring (matVecMul ring A r) (gadgetMul ring base m)

/-- Gadget-embedded blinded Ajtai commitments as `CommitmentScheme`. -/
def gadgetCommitmentScheme (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows messageDigits blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows blindCols)
      (RqVec ring (rows * messageDigits))
      (Commitment ring rows)
      (Opening ring blindCols) where
  setup := $ᵗ PublicParams ring rows blindCols
  commit A m := do
    let r ← $ᵗ Opening ring blindCols
    pure (gadgetCommitWithOpening ring base A m r, r)
  verify A m c r := decide (gadgetCommitWithOpening ring base A m r = c)

end Hiding
end Ajtai
end LatticeCrypto

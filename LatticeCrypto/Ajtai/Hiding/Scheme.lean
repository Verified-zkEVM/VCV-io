/-
Copyright (c) 2026 Tobias Rothmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import LatticeCrypto.Ajtai.Simple.Scheme
import VCVio.CryptoFoundations.CommitmentScheme

/-!
# Hiding Ajtai Commitment Scheme

Definitions for blinded Ajtai commitments and their gadget-embedded variant.
-/

open OracleComp

universe u

namespace LatticeCrypto
namespace Ajtai
namespace Hiding

variable {Coeff : Type u} [CommRing Coeff]

/-- Public parameters for blinded Ajtai commitments. -/
abbrev PublicParams (ring : NegacyclicRing Coeff) (rows blindCols : Nat) :=
  Simple.PublicParams ring rows blindCols

/-- Blinded Ajtai commitments live in the row space of the public matrix. -/
abbrev Commitment (ring : NegacyclicRing Coeff) (rows : Nat) :=
  Simple.Commitment ring rows

/-- Openings are the sampled blinding vectors. -/
abbrev Opening (ring : NegacyclicRing Coeff) (blindCols : Nat) :=
  Simple.Message ring blindCols

/-- Commit as `A * r + m`, where `r` is the opening. -/
def commitWithOpening (ring : NegacyclicRing Coeff) {rows blindCols : Nat}
    (A : PublicParams ring rows blindCols) (m : PolyVec ring.Poly rows)
    (r : Opening ring blindCols) : Commitment ring rows :=
  Simple.commit ring A r + m

/-- Verify a blinded Ajtai opening by recomputing the commitment. -/
def verify (ring : NegacyclicRing Coeff) {rows blindCols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows blindCols) (m : PolyVec ring.Poly rows)
    (c : Commitment ring rows) (r : Opening ring blindCols) : Bool :=
  commitWithOpening ring A m r == c

/-- The blinded Ajtai commitment instantiated as `CommitmentScheme`. -/
def commitmentScheme (ring : NegacyclicRing Coeff) (rows blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows blindCols)
      (PolyVec ring.Poly rows)
      (Commitment ring rows)
      (Opening ring blindCols) where
  setup := $ᵗ PublicParams ring rows blindCols
  commit A m := do
    let r ← $ᵗ Opening ring blindCols
    pure (commitWithOpening ring A m r, r)
  verify A m c r := verify ring A m c r

/-- Commit as `A * r + G * m`, where `G` is a gadget matrix. -/
def gadgetCommitWithOpening (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows messageDigits blindCols : Nat}
    (A : PublicParams ring rows blindCols) (m : PolyVec ring.Poly (rows * messageDigits))
    (r : Opening ring blindCols) : Commitment ring rows :=
  commitWithOpening ring A (gadgetMul ring base m) r

/-- Verify a gadget-embedded blinded Ajtai opening by recomputing the commitment. -/
def gadgetVerify (ring : NegacyclicRing Coeff) (base : Coeff)
    {rows messageDigits blindCols : Nat}
    [DecidableEq (Commitment ring rows)]
    (A : PublicParams ring rows blindCols) (m : PolyVec ring.Poly (rows * messageDigits))
    (c : Commitment ring rows) (r : Opening ring blindCols) : Bool :=
  verify ring A (gadgetMul ring base m) c r

/-- Gadget-embedded blinded Ajtai commitments as `CommitmentScheme`. -/
def gadgetCommitmentScheme (ring : NegacyclicRing Coeff) (base : Coeff)
    (rows messageDigits blindCols : Nat)
    [SampleableType (PublicParams ring rows blindCols)]
    [SampleableType (Opening ring blindCols)]
    [DecidableEq (Commitment ring rows)] :
    CommitmentScheme
      (PublicParams ring rows blindCols)
      (PolyVec ring.Poly (rows * messageDigits))
      (Commitment ring rows)
      (Opening ring blindCols) where
  setup := $ᵗ PublicParams ring rows blindCols
  commit A m := do
    let r ← $ᵗ Opening ring blindCols
    pure (gadgetCommitWithOpening ring base A m r, r)
  verify A m c r := gadgetVerify ring base A m c r

end Hiding
end Ajtai
end LatticeCrypto

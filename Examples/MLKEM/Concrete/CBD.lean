/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Ring

/-!
# Concrete CBD Sampling for ML-KEM

Pure-Lean executable implementation of FIPS 203 Algorithm 8 (SamplePolyCBD_η).
-/

set_option autoImplicit false

namespace MLKEM.Concrete

open MLKEM

/-- Extract the `j`-th bit (LSB = 0) of a byte. -/
private def bitOf (b : UInt8) (j : Nat) : Nat :=
  ((b >>> j.toUInt8) &&& 1).toNat

/-- FIPS 203 Algorithm 8: sample a polynomial from the centered binomial distribution CBD_η.
    Input: `64 * eta` bytes. Output: a polynomial in `R_q`. -/
def samplePolyCBD (eta : Nat) (bytes : ByteArray) : Rq :=
  let bits : Array Nat := Id.run do
    let mut b := Array.mkEmpty (bytes.size * 8)
    for k in List.range bytes.size do
      for j in List.range 8 do
        b := b.push (bitOf (bytes.get! k) j)
    return b
  Vector.ofFn fun idx =>
    let i := idx.val
    let x := (List.range eta).foldl (fun acc j =>
      acc + bits.getD (2 * i * eta + j) 0) 0
    let y := (List.range eta).foldl (fun acc j =>
      acc + bits.getD (2 * i * eta + eta + j) 0) 0
    (x : Coeff) - (y : Coeff)

end MLKEM.Concrete

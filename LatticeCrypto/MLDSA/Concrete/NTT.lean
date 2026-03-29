/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Ring

/-!
# Concrete NTT for ML-DSA

Concrete executable NTT operations for `q = 8380417`, `n = 256`, and the FIPS 204 root
`ζ = 1753`.

Implements the FIPS 204 in-place butterfly NTT (Algorithm 41) and its inverse (Algorithm 42)
exactly, using twiddle factors `ζ^(BitRev₈(k))`. The butterfly NTT output ordering matches
the reference C implementations (e.g. mldsa-native), which is essential for bitwise agreement
on key generation, signing, and verification.

Multiplication in the NTT domain is pointwise (coefficientwise).
-/

set_option autoImplicit false

namespace MLDSA.Concrete

open MLDSA

/-- Reverse the low 8 bits of `i` (FIPS 204: `brv(k)`). -/
def bitRev8 (i : Nat) : Nat :=
  let b := fun k => (i >>> k) &&& 1
  (b 0 <<< 7) ||| (b 1 <<< 6) ||| (b 2 <<< 5) ||| (b 3 <<< 4) |||
  (b 4 <<< 3) ||| (b 5 <<< 2) ||| (b 6 <<< 1) ||| b 7

/-- Precomputed twiddle table: `zetas[k] = ζ^(brv(k))` for `k = 0 .. 255`,
where `brv` is 8-bit reversal per FIPS 204 §4.5.
The forward NTT uses indices 1..255; the inverse NTT uses the same indices
(negated) in reverse order 255..1. -/
def zetaTable : Array Coeff :=
  (Array.range 256).map fun i => zeta ^ bitRev8 i

/-- `256⁻¹ mod q`. -/
def nInv : Coeff := ((modulus - (modulus - 1) / ringDegree : ℕ) : Coeff)

/-- FIPS 204 Algorithm 41 — forward NTT (in-place Cooley–Tukey butterfly).

Twiddle factors are accessed via `ζ^(BitRev₈(k))` with `k` counting from 1 to 255.
The eight stages halve `len` from 128 down to 1. -/
def butterflyNTT (f : Rq) : Tq := Id.run do
  let mut a := f.toArray
  let mut k := 1
  let mut len := 128
  while len ≥ 1 do
    let mut start := 0
    while start < ringDegree do
      let z := zetaTable.getD k 0
      k := k + 1
      for j in [start : start + len] do
        let u := a.getD j 0
        let v := a.getD (j + len) 0
        let t := z * v
        a := a.set! (j + len) (u - t)
        a := a.set! j (u + t)
      start := start + 2 * len
    len := len / 2
  return ⟨Vector.ofFn fun i => a.getD i.val 0⟩

/-- FIPS 204 Algorithm 42 — inverse NTT (in-place Gentleman–Sande butterfly).

Twiddle factors are accessed in reverse, negated. The eight stages double `len` from 1
to 128. A final scaling by `256⁻¹ mod q` restores the coefficient norm. -/
def butterflyInvNTT (fHat : Tq) : Rq := Id.run do
  let mut a := fHat.coeffs.toArray
  let mut k := 255
  let mut len := 1
  while len ≤ 128 do
    let mut start := 0
    while start < ringDegree do
      let z := -(zetaTable.getD k 0)
      k := k - 1
      for j in [start : start + len] do
        let u := a.getD j 0
        let v := a.getD (j + len) 0
        a := a.set! j (u + v)
        a := a.set! (j + len) (z * (u - v))
      start := start + 2 * len
    len := len * 2
  for j in [0 : ringDegree] do
    a := a.set! j (nInv * a.getD j 0)
  return Vector.ofFn fun i => a.getD i.val 0

/-- Pointwise multiplication in the ML-DSA NTT domain. -/
def multiplyNTTs (fHat gHat : Tq) : Tq :=
  ⟨Vector.ofFn fun i => fHat[i.val] * gHat[i.val]⟩

/-! ## Public API -/

def ntt (f : Rq) : Tq := butterflyNTT f

def invNTT (fHat : Tq) : Rq := butterflyInvNTT fHat

/-- Concrete `NTTRingOps` instance for ML-DSA. -/
def concreteNTTRingOps : NTTRingOps where
  ntt := ntt
  invNTT := invNTT
  multiplyNTTs := multiplyNTTs

end MLDSA.Concrete

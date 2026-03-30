/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Ring

/-!
# Concrete NTT for Falcon

Concrete executable NTT operations for `q = 12289`, parameterized by ring degree `n`.
Falcon uses `n ∈ {512, 1024}` (logn ∈ {9, 10}).

The NTT splits `R_q = ℤ_q[x]/(x^n + 1)` into `n` linear factors since
`q ≡ 1 mod 2n` for both parameter sets (`12289 = 12·1024 + 1`).

Implements in-place Cooley–Tukey (forward) and Gentleman–Sande (inverse) butterflies,
with twiddle factors `ζ^(brv(k))` where `ζ` is a primitive `2n`-th root of unity mod `q`.

`11` is a primitive root mod `12289` (order `12288 = 2^12 · 3`), so:
- For `n = 1024`: `ζ = 11^(12288/2048) = 11^6 mod 12289`
- For `n = 512`:  `ζ = 11^(12288/1024) = 11^12 mod 12289`
-/

set_option autoImplicit false

namespace Falcon.Concrete

open Falcon

private def primitiveRoot2N (logn : ℕ) : Coeff :=
  (11 : Coeff) ^ ((modulus - 1) / (2 * (2 ^ logn)))

private def bitRevN (logn : ℕ) (i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut v := i
  for k in [0:logn] do
    r := r ||| ((v &&& 1) <<< (logn - 1 - k))
    v := v >>> 1
  return r

def zetaTable (logn : ℕ) : Array Coeff :=
  let n := 2 ^ logn
  let z := primitiveRoot2N logn
  (Array.range n).map fun i => z ^ bitRevN logn i

def nInv (logn : ℕ) : Coeff :=
  let n := (2 ^ logn : ℕ)
  ((modulus - (modulus - 1) / n : ℕ) : Coeff)

def butterflyNTT (logn : ℕ) (f : Rq (2 ^ logn)) : Tq (2 ^ logn) := Id.run do
  let n := 2 ^ logn
  let table := zetaTable logn
  let mut a := f.toArray
  let mut k := 1
  let mut len := n / 2
  while len ≥ 1 do
    let mut start := 0
    while start < n do
      let z := table.getD k 0
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

def butterflyInvNTT (logn : ℕ) (fHat : Tq (2 ^ logn)) : Rq (2 ^ logn) := Id.run do
  let n := 2 ^ logn
  let table := zetaTable logn
  let mut a := fHat.coeffs.toArray
  let mut k := n - 1
  let mut len := 1
  while len ≤ n / 2 do
    let mut start := 0
    while start < n do
      let z := -(table.getD k 0)
      k := k - 1
      for j in [start : start + len] do
        let u := a.getD j 0
        let v := a.getD (j + len) 0
        a := a.set! j (u + v)
        a := a.set! (j + len) (z * (u - v))
      start := start + 2 * len
    len := len * 2
  let scale := nInv logn
  for j in [0 : n] do
    a := a.set! j (scale * a.getD j 0)
  return Vector.ofFn fun i => a.getD i.val 0

def multiplyNTTs {n : ℕ} (fHat gHat : Tq n) : Tq n :=
  ⟨Vector.ofFn fun i => fHat[i.val] * gHat[i.val]⟩

/-! ## Public API -/

def ntt (logn : ℕ) (f : Rq (2 ^ logn)) : Tq (2 ^ logn) := butterflyNTT logn f

def invNTT (logn : ℕ) (fHat : Tq (2 ^ logn)) : Rq (2 ^ logn) :=
  butterflyInvNTT logn fHat

def concreteNTTRingOps (logn : ℕ) : NTTRingOps (2 ^ logn) where
  ntt := ntt logn
  invNTT := invNTT logn
  multiplyNTTs := multiplyNTTs

end Falcon.Concrete

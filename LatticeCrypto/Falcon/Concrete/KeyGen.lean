/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FFT

/-!
# Concrete Falcon Key Generation

NTRU equation solver and Falcon tree construction using 64-bit fixed-point
arithmetic (no floating-point), based on Pornin 2025 (eprint 2025/1239).

## NTRU Equation Solving

Given short polynomials `(f, g)` with `gcd(f, g) = 1` in `ℤ[x]/(x^n + 1)`,
compute `(F, G)` satisfying the NTRU equation `fG - gF = q`.

The algorithm uses:
- 64-bit **fixed-point arithmetic** (32 integer + 32 fractional bits) for
  polynomial GCD/division in the Reduce step
- Multi-precision integer arithmetic (`mp31`) for exact computations
- Recursive halving of the degree (Field norm) to reduce to a scalar equation

## Tree Construction

Build the `FPRTree` from the NTRU basis `[[g, -f], [G, -F]]`:
- Gram-Schmidt orthogonalization using FPR arithmetic
- LDL decomposition of the Gram matrix
- Recursive splitting yields `σ` values at tree leaves

## References

- c-fn-dsa: `kgen.c`, `kgen_ntru.c`, `kgen_fxp.c`, `kgen_mp31.c`
- Pornin 2025 (eprint 2025/1239)
- Falcon specification v1.2, Algorithms 4–9
-/

set_option autoImplicit false

namespace Falcon.Concrete.KeyGen

open Falcon.Concrete.FPR
open Falcon.Concrete.FFTOps

/-! ## Fixed-point arithmetic (32.32 format) -/

abbrev FXP := UInt64

namespace FXP

def ofInt (x : Int32) : FXP := x.toUInt32.toUInt64 <<< 32

def toInt (x : FXP) : Int32 := (x >>> 32).toUInt32.toInt32

def mul (x y : FXP) : FXP :=
  let xn := x.toNat
  let yn := y.toNat
  ((xn * yn) >>> 32).toUInt64

def div (x y : FXP) : FXP :=
  ((x.toNat <<< 32) / y.toNat).toUInt64

end FXP

/-! ## NTRUGen: generate short NTRU polynomials -/

def ntruGen (logn : Nat) (seed : ByteArray) :
    Array Int32 × Array Int32 := sorry

/-! ## NTRU equation solver -/

def solveNTRU (logn : Nat) (f g : Array Int32) :
    Option (Array Int32 × Array Int32) := sorry

/-! ## Full key generation -/

structure RawKeyPair where
  f : Array Int32
  g : Array Int32
  capF : Array Int32
  capG : Array Int32
  h : Array UInt16
  tree : FPRTree 0

def keyGen (logn : Nat) (seed : ByteArray) : Option RawKeyPair := sorry

end Falcon.Concrete.KeyGen

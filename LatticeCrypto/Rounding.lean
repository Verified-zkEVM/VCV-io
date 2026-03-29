/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Norm

/-!
# Rounding and Decomposition for Lattice Cryptography

This file defines the abstract rounding and decomposition operations used in lattice-based
signature schemes: `highBits`, `lowBits`, `power2Round`, `makeHint`, and `useHint`.
These operations are central to ML-DSA (FIPS 204 / CRYSTALS-Dilithium).

The interface is axiomatized following the EasyCrypt formalization in `DRing.eca`
(formosa-crypto/dilithium), which captures the minimal algebraic properties needed
for the security proof.

## References

- NIST FIPS 204, Section 2.4 (HighBits, LowBits, Power2Round, MakeHint, UseHint)
- EasyCrypt `DRing.eca` (abstract rounding axioms)
- Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium
  (CRYPTO 2023, ePrint 2023/246)
-/

set_option autoImplicit false

namespace LatticeCrypto

/-- Abstract rounding operations on a polynomial ring `Rq`, parameterized by a
rounding modulus `α` (typically `2 * γ₂` in ML-DSA). The `High` type represents
the image of `highBits`, and `Hint` represents the hint type for `useHint`.

The operations decompose ring elements into high-order and low-order parts,
and provide a hint mechanism for recovering the correct high-order bits from
a perturbed element. -/
structure RoundingOps (Rq : Type*) (α : ℕ) where
  /-- The type of high-order representatives. -/
  High : Type*
  /-- The type of hint values. -/
  Hint : Type*
  /-- Extract the low-order part of `r` with respect to rounding modulus `α`. -/
  lowBits : Rq → Rq
  /-- Extract the high-order representative of `r` with respect to rounding modulus `α`. -/
  highBits : Rq → High
  /-- Reconstruct the high-order contribution from a `High` representative. -/
  shift : High → Rq
  /-- Produce a hint that allows recovery of `highBits(r + z)` from `r` alone. -/
  makeHint : Rq → Rq → Hint
  /-- Use a hint to recover the high-order bits of a perturbed value. -/
  useHint : Hint → Rq → High

/-- Abstract power-2 rounding operations, parameterized by the number of
dropped bits `d`. Used in ML-DSA for splitting `t = t1 * 2^d + t0`. -/
structure Power2RoundOps (Rq : Type*) (d : ℕ) where
  /-- The type of high-order (power-2 rounded) representatives. -/
  Power2High : Type*
  /-- Round `r` by dropping the `d` lowest bits. -/
  power2Round : Rq → Power2High
  /-- Reconstruct from the rounded representative. -/
  shift2 : Power2High → Rq

/-- Algebraic laws for `RoundingOps`, capturing the properties required by the
Dilithium/ML-DSA security proof. These correspond to the axioms in EasyCrypt's
`DRing.eca` `HighLow` theory. -/
structure RoundingOps.Laws {Rq : Type*} [AddCommGroup Rq]
    {α : ℕ} (ops : RoundingOps Rq α)
    (cInfNorm : Rq → ℕ) : Prop where
  /-- Decomposition identity: the high and low parts sum to the original element. -/
  high_low_decomp : ∀ x : Rq, ops.shift (ops.highBits x) + ops.lowBits x = x
  /-- The low-order part is bounded by `α / 2`. -/
  lowBits_bound : ∀ r : Rq, cInfNorm (ops.lowBits r) ≤ α / 2
  /-- If the perturbation `s` is small enough relative to the low-order part of `r`,
  then adding `s` does not change the high-order bits. -/
  hide_low : ∀ (r s : Rq) (b : ℕ),
    cInfNorm s ≤ b → cInfNorm (ops.lowBits r) < α / 2 - b →
    ops.highBits (r + s) = ops.highBits r
  /-- `shift` is injective on the image of `highBits`. -/
  shift_injective : Function.Injective ops.shift
  /-- `useHint` correctly recovers `highBits (r + z)` when `z` is small enough. -/
  useHint_correct : ∀ (z r : Rq),
    cInfNorm z ≤ α / 2 →
    ops.useHint (ops.makeHint z r) r = ops.highBits (r + z)
  /-- The reconstruction from `useHint` is within `α + 1` of the original. -/
  useHint_bound : ∀ (r : Rq) (h : ops.Hint),
    cInfNorm (r - ops.shift (ops.useHint h r)) ≤ α + 1

/-- Algebraic laws for `Power2RoundOps`. -/
abbrev Power2RoundOps.Laws {Rq : Type*} [AddCommGroup Rq]
    {d : ℕ} (ops : Power2RoundOps Rq d)
    (cInfNorm : Rq → ℕ) : Prop :=
  ∀ r : Rq, cInfNorm (r - ops.shift2 (ops.power2Round r)) ≤ 2 ^ (d - 1)

end LatticeCrypto

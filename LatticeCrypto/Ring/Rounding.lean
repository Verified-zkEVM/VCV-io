/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Ring.Kernel

/-!
# Rounding And Decomposition For Negacyclic Rings

Abstract rounding and decomposition interfaces for lattice signature schemes,
parameterized by a `NegacyclicRing`. Defines:

- `RoundingOps`: the ML-DSA-style high/low-bit decomposition and hint
  mechanism, parameterized by a rounding modulus `α` (typically `2 · γ₂`).
- `Power2RoundOps`: the power-of-two rounding used for ML-DSA public-key
  compression, parameterized by the number of dropped bits `d`.
- `RoundingOps.Laws` / `Power2RoundOps.Laws`: algebraic correctness
  properties (decomposition identity, norm bounds, hint injectivity).

Concrete implementations live in `MLDSA.Concrete.Rounding`. The abstract
interfaces are consumed by `MLDSA.Scheme` and `MLDSA.Signature`.
-/


namespace LatticeCrypto

/-- Abstract rounding operations on a `NegacyclicRing`, parameterized by a
rounding modulus `α` (typically `2 · γ₂` in the ML-DSA specification).

Bundles the `highBits` / `lowBits` decomposition, the `shift` embedding,
and the `makeHint` / `useHint` pair used by ML-DSA signing and verification
to recover `w₁` from a hint vector. -/
structure RoundingOps {Coeff : Type*} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) (α : ℕ) where
  High : Type*
  Hint : Type*
  lowBits : ring.Poly → ring.Poly
  highBits : ring.Poly → High
  shift : High → ring.Poly
  makeHint : ring.Poly → ring.Poly → Hint
  useHint : Hint → ring.Poly → High

/-- Abstract power-2 rounding operations, parameterized by the number of dropped bits `d`. -/
structure Power2RoundOps {Coeff : Type*} [CommRing Coeff]
    (ring : NegacyclicRing Coeff) (d : ℕ) where
  Power2High : Type*
  power2Round : ring.Poly → Power2High
  shift2 : Power2High → ring.Poly

/-- Algebraic laws for `RoundingOps`. -/
structure RoundingOps.Laws {Coeff : Type*} [CommRing Coeff]
    {ring : NegacyclicRing Coeff} [AddCommGroup ring.Poly]
    {α : ℕ} (ops : RoundingOps ring α) (cInfNorm : ring.Poly → ℕ) : Prop where
  high_low_decomp : ∀ x : ring.Poly, ops.shift (ops.highBits x) + ops.lowBits x = x
  lowBits_bound : ∀ r : ring.Poly, cInfNorm (ops.lowBits r) ≤ α / 2
  hide_low : ∀ (r s : ring.Poly) (b : ℕ),
    cInfNorm s ≤ b → cInfNorm (ops.lowBits r) + b < α / 2 →
    ops.highBits (r + s) = ops.highBits r
  shift_injective : Function.Injective ops.shift
  useHint_correct : ∀ (z r : ring.Poly),
    cInfNorm z ≤ α / 2 →
    ops.useHint (ops.makeHint z r) r = ops.highBits (r + z)
  useHint_bound : ∀ (r : ring.Poly) (h : ops.Hint),
    cInfNorm (r - ops.shift (ops.useHint h r)) ≤ α + 1

/-- Algebraic laws for `Power2RoundOps`. -/
structure Power2RoundOps.Laws {Coeff : Type*} [CommRing Coeff]
    {ring : NegacyclicRing Coeff} [AddCommGroup ring.Poly]
    {d : ℕ} (ops : Power2RoundOps ring d) (cInfNorm : ring.Poly → ℕ) : Prop where
  power2Round_bound : ∀ r : ring.Poly,
    cInfNorm (r - ops.shift2 (ops.power2Round r)) ≤ 2 ^ (d - 1)

end LatticeCrypto

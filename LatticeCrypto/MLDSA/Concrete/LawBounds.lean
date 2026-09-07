/-
Copyright (c) 2026 Quang Dao, Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Oleksandr Vovkotrub
-/

module

import all LatticeCrypto.MLDSA.Concrete.Encoding
public import LatticeCrypto.MLDSA.Concrete.Encoding
public import LatticeCrypto.MLDSA.Concrete.NTT
public import LatticeCrypto.MLDSA.Concrete.Rounding

/-!
# Algebraic Range Bounds Behind the Concrete ML-DSA Primitive Laws

The `MLDSA.Primitives.Laws` fields of the concrete FIPS 204 bundle split into two kinds of
obligation: range and roundtrip facts about the rounding, NTT, and byte-encoding layers, which are
ordinary algebra over `Rq`; and facts about the SHAKE-driven samplers, which only make sense once
the XOF wiring is in scope. This file holds the first kind, so that it stays inside the proof
library and away from the native `@[extern]` surface.

## Contents

- `polyNorm_eq_cInfNorm`: the ML-DSA centered infinity norm `polyNorm` is the backend-generic
  `LatticeCrypto.cInfNorm` on the canonical vector backend. This bridge lets the `polyNorm`-stated
  `Primitives.Laws` fields consume the `cInfNorm`-stated lemmas of `Ring/Norms.lean` and
  `Concrete/Rounding.lean`.
- `concrete_transform`: the `Primitives.Laws.transform` field, i.e. the concrete `NTTRingLaws`
  witness of `Concrete/NTT.lean`, restated under the `concrete_*` naming used for the law fields.
- `bitUnpackPoly_z_cInfNorm_le`: every coefficient produced by a `z`-range `bitUnpackPoly` has
  centered absolute value at most `γ`. This is a property of the decoder's output window
  (`bitUnpackPoly_get`) and holds for an arbitrary byte input, so it is independent of which byte
  stream the caller supplies.
- `approved_gamma1_width`: the `z`-range bit width of each approved parameter set satisfies
  `2 ^ width = 2 γ₁` and `2 γ₁ < q`, the two side conditions of the previous bound.
- `highBits_coeff_val_lt_width`: every approved-parameter `highBits` coefficient fits in the bit
  width used by the `w₁` packer, which is what makes `simpleBitPackPoly` invertible on the valid
  commitment range.

The `Primitives.Laws` fields that mention the assembled bundle `MLDSA.Concrete.concretePrimitives`
are proven in `Extern/MLDSA/Laws.lean`, on top of the lemmas banked here.
-/

@[expose] public section


namespace MLDSA.Concrete

open MLDSA LatticeCrypto

/-- The ML-DSA centered infinity norm `polyNorm` agrees with the backend-generic
`LatticeCrypto.cInfNorm` on the canonical vector backend. This is the bridge that lets the
`polyNorm`-stated `Primitives.Laws` fields consume the `cInfNorm`-stated rounding lemmas. -/
theorem polyNorm_eq_cInfNorm (f : Rq) : polyNorm f = LatticeCrypto.cInfNorm f := by
  exact LatticeCrypto.zmodPolyNormOps_cInfNorm f

variable (p : Params)

/-- `Primitives.Laws.transform` for the concrete instance. -/
theorem concrete_transform : NTTRingLaws concreteNTTRingOps :=
  concreteNTTRingLaws

/-! ## Decode range of the `z`-window bit unpacker

The concrete `expandMask` decodes each coefficient through `polyZUnpack p`, i.e.
`bitUnpackPoly bytes (-γ₁ + 1) γ₁`. By the decode-range bound `bitUnpackPoly_get`, every coefficient
is `γ₁ - v` for a `width`-bit value `v` with `width = rangeWidth (-γ₁ + 1) γ₁`. For the approved
parameter sets `2 ^ width = 2 γ₁`, so `v ≤ 2 γ₁ - 1` and `γ₁ - v ∈ [-(γ₁ - 1), γ₁]`, whose centered
representative (since `2 γ₁ < q`) is `γ₁ - v` itself, of absolute value at most `γ₁`. The argument
is purely about the decoder's output range and holds for any byte input. -/

/-- Decode-range infinity-norm bound for a `z`-range `bitUnpackPoly`: every coefficient of
`bitUnpackPoly bytes (-γ + 1) γ` has centered absolute value at most `γ`, provided the bit width
satisfies `2 ^ width = 2 γ` (true for FIPS-204 `γ₁`, a power of two) and `2 γ < q`. -/
theorem bitUnpackPoly_z_cInfNorm_le (bytes : ByteArray) (γ : ℕ)
    (hwidth : (2 : ℕ) ^ rangeWidth (-(γ : ℤ) + 1) (γ : ℤ) = 2 * γ)
    (hq : 2 * γ < modulus) :
    LatticeCrypto.cInfNorm (bitUnpackPoly bytes (-(γ : ℤ) + 1) (γ : ℤ)) ≤ γ := by
  rw [LatticeCrypto.cInfNorm_le_iff]
  intro i
  obtain ⟨v, hv, hget⟩ := bitUnpackPoly_get bytes (-(γ : ℤ) + 1) (γ : ℤ) i
  rw [hget, hwidth] at *
  have hbound : ((γ : ℤ) - (v : ℤ)).natAbs ≤ γ := by omega
  rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le ((γ : ℤ) - (v : ℤ)) hbound (by omega)]
  exact hbound

/-- For each approved parameter set the `z`-range bit width satisfies `2 ^ width = 2 γ₁` (because
`γ₁` is a power of two) and `2 γ₁ < q`. -/
theorem approved_gamma1_width (hp : p.isApproved) :
    (2 : ℕ) ^ rangeWidth (-(p.gamma1 : ℤ) + 1) (p.gamma1 : ℤ) = 2 * p.gamma1 ∧
      2 * p.gamma1 < modulus := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩

/-! ## Bit-width fit for the `w₁` packer

The concrete `w1Encode` packs each `High` coefficient via `simpleBitPackPoly` at the bit width
`simpleWidth ((q-1)/(2γ₂) - 1)`. On the valid commitment range — every component an actual
`highBits` output — each coefficient lies in `[0, (q-1)/(2γ₂) - 1]` (`highBits_coeff_val_lt_m`),
which fits in that bit width, so the packer is inverted by `simpleBitUnpackPoly` and is injective
there. -/

/-- Every approved-parameter `highBits` coefficient fits in the `w₁` packer's bit width. -/
theorem highBits_coeff_val_lt_width (hp : p.isApproved) (r : Rq) (c : Fin ringDegree) :
    ((MLDSA.Concrete.highBits p r).get c).val
      < 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
  have hlt : ((MLDSA.Concrete.highBits p r).get c).val < (modulus - 1) / (2 * p.gamma2) :=
    MLDSA.Concrete.highBits_coeff_val_lt_m p hp r c
  -- `(q-1)/(2γ₂) ≤ 2 ^ simpleWidth ((q-1)/(2γ₂) - 1)`.
  have hwin : (modulus - 1) / (2 * p.gamma2)
      ≤ 2 ^ MLDSA.Concrete.simpleWidth ((modulus - 1) / (2 * p.gamma2) - 1) := by
    rcases hp with rfl | rfl | rfl <;> decide
  omega

end MLDSA.Concrete

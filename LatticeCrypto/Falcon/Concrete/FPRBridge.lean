/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Batteries.Data.Rat.Float
import LatticeCrypto.Falcon.Scheme
import LatticeCrypto.Falcon.Concrete.FPR
import LatticeCrypto.Falcon.Concrete.Instance
import LatticeCrypto.Falcon.Concrete.Encoding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# FPR ↔ ℝ Bridge Theorems

Error bounds connecting the integer-only FPR emulation layer to the
exact `ℝ` arithmetic used in the abstract Falcon specification.

The analytic error bounds in this file are still stated as proof obligations.
The end-to-end verifier bridge is reduced to explicit codec and fast-kernel
correctness assumptions so the remaining gap is spelled out precisely.

## Per-Operation Error Bounds

Each FPR arithmetic operation introduces at most a relative error of
`2^{-52}` (matching IEEE-754 binary64 precision):

- `|fpr_add(a, b) - (a_real + b_real)| ≤ 2^{-52} · |a_real + b_real|`
- `|fpr_mul(a, b) - a_real · b_real| ≤ 2^{-52} · |a_real · b_real|`

## Accumulated Error in ffSampling

The statistical distance between the FPR-based sampler output and the
ideal discrete Gaussian is bounded by the Rényi divergence analysis
from Pornin 2019, Section 3:

  `R_∞(D_FPR ‖ D_ideal) ≤ 1 + ε_renyi`

where `ε_renyi < 2^{-64}` for 53-bit mantissa precision.

## References

- Pornin 2019 (eprint 2019/893), Section 3 (precision analysis)
- Falcon specification v1.2, Section 2.5.2 (sampler quality)
-/


namespace Falcon.Concrete.FPRBridge

open Falcon.Concrete.FPR

noncomputable section

/-! ## Interpretation: FPR → ℝ -/

/-- Interpret an `FPR` word as the corresponding IEEE-754 value in `ℝ`,
mapping non-finite bit patterns to `0`. -/
def toReal (x : FPR) : ℝ := ((Float.ofBits x).toRat0 : ℝ)

/-! ## Verification-only concrete primitives -/

/-- Concrete primitive bundle restricted to the fields used by `Falcon.verify`.
The sampler and FFT bridge fields are dummy placeholders because verification never
invokes them. -/
def verifyPrimitives (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) : Falcon.Primitives p where
  publicKeyBytes := fun h => Falcon.Concrete.publicKeyBytes p.logn h
  hashToPoint := fun salt pkBytes msg => Falcon.Concrete.hashToPoint p.n salt pkBytes msg
  samplerZ := fun _ _ => pure 0
  fftTarget := fun _ => 0
  fftInt := fun _ => 0
  ifftRound := fun _ => 0
  compress := Falcon.Concrete.compress p.n
  decompress := Falcon.Concrete.decompress p.n
  nttOps := hn ▸ Falcon.Concrete.concreteNTTRingOps p.logn

/-! ## Per-operation error bounds -/

/-- Relative error bound for `FPR.add`. -/
theorem add_error (a b : FPR) :
    |toReal (FPR.add a b) - (toReal a + toReal b)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a + toReal b| := by
  sorry

/-- Relative error bound for `FPR.mul`. -/
theorem mul_error (a b : FPR) :
    |toReal (FPR.mul a b) - toReal a * toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a * toReal b| := by
  sorry

/-- Relative error bound for `FPR.div`. -/
theorem div_error (a b : FPR) (hb : toReal b ≠ 0) :
    |toReal (FPR.div a b) - toReal a / toReal b| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * |toReal a / toReal b| := by
  sorry

/-- Relative error bound for `FPR.sqrt`. -/
theorem sqrt_error (a : FPR) (ha : 0 ≤ toReal a) :
    |toReal (FPR.sqrt a) - Real.sqrt (toReal a)| ≤
    (2 : ℝ) ^ (-(52 : ℤ)) * Real.sqrt (toReal a) := by
  sorry

/-! ## Sampler quality -/

/-- Absolute approximation bound for the FACCT-based `expm_p63` routine. -/
theorem expm_p63_error (x ccs : FPR)
    (hx : 0 ≤ toReal x) (hx' : toReal x < Real.log 2) :
    abs ((((FPR.expm_p63 x ccs).toNat : ℕ) : ℝ) / (2 : ℝ) ^ 63 -
      (toReal ccs * Real.exp (-(toReal x)))) ≤
    (2 : ℝ) ^ (-(51 : ℤ)) := by
  sorry

/-! ## End-to-end correctness -/

/-- The concrete Falcon verifier agrees with the abstract verifier once the concrete signature
codec, public-key codec, and fast arithmetic kernels are related to their specification-level
counterparts. The abstract verifier is instantiated with the same concrete verification fields. -/
theorem concrete_verify_eq_verify
    (p : Falcon.Params) (hn : p.n = 2 ^ p.logn) (hsbytelen : 0 < p.sbytelen)
    (hverifyEmpty : ∀ (pkBytes : ByteArray) (salt : Bytes 40) (msg : List Byte),
      Falcon.Concrete.concreteVerify p pkBytes msg
        (Falcon.Concrete.sigEncode salt [] p.logn) = false)
    (hsigDecode : ∀ (salt : Bytes 40) (compSig : List Byte),
      compSig ≠ [] →
        Falcon.Concrete.sigDecode (Falcon.Concrete.sigEncode salt compSig p.logn) p.logn =
          some (salt, compSig))
    (hpkDecode : ∀ h : Falcon.Rq p.n,
      Falcon.Concrete.pkDecode p.n
        ((Falcon.Concrete.publicKeyBytes p.logn h).extract 1
          (Falcon.Concrete.publicKeyBytes p.logn h).size) = some h)
    (hmul : ∀ s2 h : Falcon.Rq p.n,
      Falcon.Concrete.negacyclicMulU32 s2 h = Falcon.negacyclicMul s2 h)
    (hnorm : ∀ s1 s2 : Falcon.Rq p.n,
      Falcon.Concrete.pairL2NormSqU32 s1 s2 = Falcon.pairL2NormSq s1 s2)
    (pk : Falcon.PublicKey p) (msg : List Falcon.Byte) (sig : Falcon.Signature) :
    let prims := verifyPrimitives p hn;
    Falcon.Concrete.concreteVerify p (prims.publicKeyBytes pk.h) msg
      (Falcon.Concrete.sigEncode sig.salt sig.compressedS2 p.logn) =
        Falcon.verify p prims pk msg sig := by
  dsimp
  by_cases hcomp : sig.compressedS2 = []
  · have hslen : sig.compressedS2.length < p.sbytelen := by
      simpa [hcomp] using hsbytelen
    have hdecomp : (verifyPrimitives p hn).decompress [] p.sbytelen = none := by
      simp [verifyPrimitives, Falcon.Concrete.decompress, hsbytelen]
    have hleft := hverifyEmpty ((verifyPrimitives p hn).publicKeyBytes pk.h) sig.salt msg
    have hright : Falcon.verify p (verifyPrimitives p hn) pk msg sig = false := by
      simp [Falcon.verify, hcomp, hdecomp]
    simpa [hcomp] using hleft.trans hright.symm
  · simp [Falcon.Concrete.concreteVerify, Falcon.verify,
      hsigDecode sig.salt sig.compressedS2 hcomp, Falcon.Primitives.hashToPointForPublicKey,
      verifyPrimitives, hpkDecode, hmul, hnorm]
    rfl

end

end Falcon.Concrete.FPRBridge

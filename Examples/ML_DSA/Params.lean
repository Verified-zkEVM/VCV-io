/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.Constructions.SampleableType

/-!
# ML-DSA Parameters

This file collects the fixed constants and approved parameter sets from FIPS 204.
The development stays generic over the variable parameters while exposing the three
named NIST-approved instantiations.

## References

- NIST FIPS 204, Section 4 (Table 1: ML-DSA parameter sets)
-/

set_option autoImplicit false

namespace ML_DSA

abbrev Byte := UInt8

abbrev Bytes (n : ℕ) := Vector Byte n

/-- The variable parameters that distinguish the approved ML-DSA instantiations. -/
structure Params where
  /-- Number of rows in the matrix A. -/
  k : ℕ
  /-- Number of columns in the matrix A. -/
  l : ℕ
  /-- Private key coefficient range: secret vectors have coefficients in [-η, η]. -/
  eta : ℕ
  /-- Number of ±1 coefficients in the challenge polynomial c. -/
  tau : ℕ
  /-- Collision strength of c̃ (in bits). -/
  lambda : ℕ
  /-- Coefficient range of the masking vector y: coefficients in [-(γ₁-1), γ₁-1]. -/
  gamma1 : ℕ
  /-- Low-order rounding range: 2*γ₂ divides q-1. -/
  gamma2 : ℕ
  /-- Maximum number of 1's in the hint vector h. -/
  omega : ℕ
deriving Repr, DecidableEq

/-- The fixed ring degree used by FIPS 204. -/
def ringDegree : ℕ := 256

/-- The fixed modulus used by FIPS 204: q = 2^23 - 2^13 + 1 = 8380417. -/
def modulus : ℕ := 8380417

/-- The distinguished root of unity: ζ = 1753 is a 512th root of unity in Z_q. -/
def zeta : ZMod modulus := 1753

/-- Number of dropped bits from t in Power2Round: d = 13. -/
def droppedBits : ℕ := 13

namespace Params

/-- β = τ · η, the bound on ‖c · s‖∞ used in rejection sampling. -/
def beta (params : Params) : ℕ := params.tau * params.eta

/-- Size of the public key in bytes. -/
def publicKeyBytes (params : Params) : ℕ :=
  32 + 32 * params.k * (Nat.log2 (modulus - 1) + 1 - droppedBits)

/-- Size of the private key in bytes. -/
def secretKeyBytes (params : Params) : ℕ :=
  32 + 32 + 64 +
  32 * params.l * (Nat.log2 (2 * params.eta) + 1) +
  32 * params.k * (Nat.log2 (2 * params.eta) + 1) +
  32 * params.k * droppedBits

/-- Size of a signature in bytes. -/
def signatureBytes (params : Params) : ℕ :=
  params.lambda / 4 +
  32 * params.l * (1 + Nat.log2 (params.gamma1 - 1)) +
  params.omega + params.k

end Params

/-- The approved named parameter sets from FIPS 204. -/
inductive ParameterSet where
  | ML_DSA_44
  | ML_DSA_65
  | ML_DSA_87
deriving Repr, DecidableEq

namespace ParameterSet

/-- Interpret a named parameter set as the corresponding parameter record. -/
def params : ParameterSet → Params
  | .ML_DSA_44 => {
      k := 4, l := 4, eta := 2, tau := 39, lambda := 128,
      gamma1 := 2^17, gamma2 := (modulus - 1) / 88, omega := 80 }
  | .ML_DSA_65 => {
      k := 6, l := 5, eta := 4, tau := 49, lambda := 192,
      gamma1 := 2^19, gamma2 := (modulus - 1) / 32, omega := 55 }
  | .ML_DSA_87 => {
      k := 8, l := 7, eta := 2, tau := 60, lambda := 256,
      gamma1 := 2^19, gamma2 := (modulus - 1) / 32, omega := 75 }

/-- Required RBG security strength from FIPS 204 Section 3.6.1. -/
def requiredRBGStrength : ParameterSet → ℕ
  | .ML_DSA_44 => 128
  | .ML_DSA_65 => 192
  | .ML_DSA_87 => 256

/-- NIST security category. -/
def securityCategory : ParameterSet → ℕ
  | .ML_DSA_44 => 2
  | .ML_DSA_65 => 3
  | .ML_DSA_87 => 5

end ParameterSet

def mldsa44 : Params := ParameterSet.params .ML_DSA_44
def mldsa65 : Params := ParameterSet.params .ML_DSA_65
def mldsa87 : Params := ParameterSet.params .ML_DSA_87

/-- Recognize the approved FIPS 204 parameter sets. -/
def Params.isApproved (params : Params) : Prop :=
  params = mldsa44 ∨ params = mldsa65 ∨ params = mldsa87

end ML_DSA

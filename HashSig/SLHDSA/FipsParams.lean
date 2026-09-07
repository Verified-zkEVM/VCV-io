/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Params

/-!
# SLH-DSA FIPS Parameter Compatibility Facts

Derived widths, security categories, and family-aware lookup over the canonical
`FipsParameterSet` enumeration. The arithmetic validity boundary remains `Params.Valid`; this
module does not add a second approval predicate or parameter-set enumeration.
-/

@[expose] public section

namespace SLHDSA

/-- Independently recorded FIPS 205 component widths not carried by `FipsExpectedSizes`. -/
structure FipsComponentSizes where
  /-- Bytes of the digest consumed by FORS. -/
  forsDigest : ℕ
  /-- Bytes selecting the lowest-layer XMSS tree. -/
  treeIndex : ℕ
  /-- Bytes selecting the WOTS+/FORS leaf. -/
  leafIndex : ℕ
deriving Repr, DecidableEq, BEq

namespace FipsParameterSet

/-- NIST security category associated with a FIPS 205 parameter-set name. -/
def category : FipsParameterSet → ℕ
  | .SLHDSA_SHA2_128s | .SLHDSA_SHA2_128f
  | .SLHDSA_SHAKE_128s | .SLHDSA_SHAKE_128f => 1
  | .SLHDSA_SHA2_192s | .SLHDSA_SHA2_192f
  | .SLHDSA_SHAKE_192s | .SLHDSA_SHAKE_192f => 3
  | .SLHDSA_SHA2_256s | .SLHDSA_SHA2_256f
  | .SLHDSA_SHAKE_256s | .SLHDSA_SHAKE_256f => 5

/-- FIPS 205 component widths recorded independently of the arithmetic formulas. -/
def expectedComponentSizes : FipsParameterSet → FipsComponentSizes
  | .SLHDSA_SHA2_128s | .SLHDSA_SHAKE_128s => ⟨21, 7, 2⟩
  | .SLHDSA_SHA2_128f | .SLHDSA_SHAKE_128f => ⟨25, 8, 1⟩
  | .SLHDSA_SHA2_192s | .SLHDSA_SHAKE_192s => ⟨30, 7, 2⟩
  | .SLHDSA_SHA2_192f | .SLHDSA_SHAKE_192f => ⟨33, 8, 1⟩
  | .SLHDSA_SHA2_256s | .SLHDSA_SHAKE_256s => ⟨39, 7, 1⟩
  | .SLHDSA_SHA2_256f | .SLHDSA_SHAKE_256f => ⟨40, 8, 1⟩

/-- The canonical list contains exactly the twelve FIPS 205 names. -/
@[simp] theorem all_length : all.length = 12 := by decide

/-- All derived digest, component, key, and signature widths agree with the independently
recorded FIPS 205 values. -/
theorem derived_widths_eq_expected (ps : FipsParameterSet) :
    ps.params.m = ps.expectedSizes.digest ∧
    ps.params.digestBytes = ps.expectedComponentSizes.forsDigest ∧
    ps.params.treeIdxBytes = ps.expectedComponentSizes.treeIndex ∧
    ps.params.leafIdxBytes = ps.expectedComponentSizes.leafIndex ∧
    ps.params.publicKeyBytes = ps.expectedSizes.publicKey ∧
    ps.params.secretKeyBytes = ps.expectedSizes.secretKey ∧
    ps.params.signatureBytes = ps.expectedSizes.signature := by
  cases ps <;> decide

/-- Every FIPS 205 row has `lgw = 4` and the corresponding exact WOTS+ chain widths. -/
theorem wots_widths (ps : FipsParameterSet) :
    ps.params.lgw = 4 ∧ ps.params.len1 = 2 * ps.params.n ∧
    ps.params.len2 = 3 ∧ ps.params.len = 2 * ps.params.n + 3 := by
  cases ps <;> decide

/-- Recover a FIPS name only when both the hash family and raw arithmetic parameters match. The
family argument distinguishes each SHA2/SHAKE pair that shares one `Params` value. -/
def ofParams (family : HashFamily) (p : Params) : Option FipsParameterSet :=
  all.find? fun ps => decide (ps.hashFamily = family ∧ ps.params = p)

/-- Family-aware lookup is an exact left inverse of every canonical FIPS parameter set. -/
@[simp] theorem ofParams_self (ps : FipsParameterSet) :
    ofParams ps.hashFamily ps.params = some ps := by
  cases ps <;> decide

end FipsParameterSet

end SLHDSA

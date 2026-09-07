/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import Mathlib.Data.Nat.Log
public import VCVio.OracleComp.Constructions.SampleableType

/-!
# SLH-DSA Parameters

Raw arithmetic parameters, their mathematical validity conditions, and the named parameter sets
for SLH-DSA (SPHINCS+, FIPS 205). `FipsParameterSet` enumerates all twelve approved FIPS 205
instantiations. The SP 800-230 reduced `SLH-DSA-SHA2-128-24` profile is kept separately in
`LimitedParameterSet`.

The Winternitz and FORS lengths are derived from the primary parameters exactly as in FIPS 205
§5 (Eqs 5.1–5.3) and §9 (the message-digest length `m`); see `Params.len1`, `Params.len2`,
`Params.len`, and `Params.m`.

## References

- NIST FIPS 205 (SLH-DSA), Sections 4, 5, 9, 10, 11 (Table 2 parameter sets)
- NIST SP 800-230 ipd (the reduced 2²⁴-usage parameter set)
-/

@[expose] public section

namespace SLHDSA

/-- Byte values used by the SLH-DSA encodings and address layout. -/
abbrev Byte := UInt8

/-- Fixed-length byte vectors used by the FIPS 205 interfaces. -/
abbrev Bytes (n : ℕ) := Vector Byte n

/-- The variable parameters that distinguish SLH-DSA instantiations (FIPS 205, Table 2). -/
structure Params where
  /-- Security parameter: hash output length in bytes (also the node size). -/
  n : ℕ
  /-- Total hypertree height. -/
  h : ℕ
  /-- Number of hypertree layers. -/
  d : ℕ
  /-- Per-XMSS-tree height `h' = h / d`. -/
  hp : ℕ
  /-- FORS tree height (each FORS tree has `2^a` leaves). -/
  a : ℕ
  /-- Number of FORS trees. -/
  k : ℕ
  /-- Bits per WOTS+ chain (`w = 2^lgw`). -/
  lgw : ℕ
deriving Repr, DecidableEq

namespace Params

/-- Mathematical well-formedness conditions shared by the generic SLH-DSA algorithms.

Hash-family-specific address bounds do not belong here; they are properties of concrete
instantiations and their reachable addresses. -/
structure Valid (p : Params) : Prop where
  /-- Hash outputs contain at least one byte. -/
  n_pos : 0 < p.n
  /-- A hypertree contains at least one layer. -/
  d_pos : 0 < p.d
  /-- Every XMSS tree has positive height. -/
  hp_pos : 0 < p.hp
  /-- Every FORS tree has positive height. -/
  a_pos : 0 < p.a
  /-- FORS contains at least one tree. -/
  k_pos : 0 < p.k
  /-- The Winternitz base exponent is positive. -/
  lgw_pos : 0 < p.lgw
  /-- WOTS+ message digits consume exactly the `n` input bytes without a zero-filled tail. -/
  wots_input_aligned : p.lgw ∣ 8 * p.n
  /-- The total height is exactly the sum of the equal-height XMSS layers. -/
  h_eq_layers : p.h = p.d * p.hp

instance (p : Params) : Decidable p.Valid :=
  if hn : 0 < p.n then
    if hd : 0 < p.d then
      if hhp : 0 < p.hp then
        if ha : 0 < p.a then
          if hk : 0 < p.k then
            if hlgw : 0 < p.lgw then
              if haligned : p.lgw ∣ 8 * p.n then
                if hh : p.h = p.d * p.hp then
                  isTrue ⟨hn, hd, hhp, ha, hk, hlgw, haligned, hh⟩
                else
                  isFalse fun h => hh h.h_eq_layers
              else
                isFalse fun h => haligned h.wots_input_aligned
            else
              isFalse fun h => hlgw h.lgw_pos
          else
            isFalse fun h => hk h.k_pos
        else
          isFalse fun h => ha h.a_pos
      else
        isFalse fun h => hhp h.hp_pos
    else
      isFalse fun h => hd h.d_pos
  else
    isFalse fun h => hn h.n_pos

/-- The Winternitz parameter `w = 2^lgw` (FIPS 205 Eq 5.1). -/
def w (p : Params) : ℕ := 2 ^ p.lgw

/-- WOTS+ message length `len1 = ⌈8n / lgw⌉` (FIPS 205 Eq 5.2). -/
def len1 (p : Params) : ℕ := (8 * p.n + p.lgw - 1) / p.lgw

/-- WOTS+ checksum length `len2 = ⌊log_w(len1·(w−1))⌋ + 1` (FIPS 205 Eq 5.3, computed via
`Nat.log` rather than the iterative `gen_len2` of Algorithm 1). -/
def len2 (p : Params) : ℕ := Nat.log p.w (p.len1 * (p.w - 1)) + 1

/-- Total number of WOTS+ chains `len = len1 + len2`. -/
def len (p : Params) : ℕ := p.len1 + p.len2

/-- Number of leaves in one FORS tree, `t = 2^a`. -/
def t (p : Params) : ℕ := 2 ^ p.a

/-- Bytes of the message digest fed to FORS, `⌈k·a / 8⌉`. -/
def digestBytes (p : Params) : ℕ := (p.k * p.a + 7) / 8

/-- Bytes selecting the lowest-layer XMSS tree, `⌈(h − h') / 8⌉`. -/
def treeIdxBytes (p : Params) : ℕ := (p.h - p.hp + 7) / 8

/-- Bytes selecting the WOTS+/FORS leaf within its tree, `⌈h / (8d)⌉`. -/
def leafIdxBytes (p : Params) : ℕ := (p.h + 8 * p.d - 1) / (8 * p.d)

/-- Length of the message digest produced by `H_msg`,
`m = ⌈k·a/8⌉ + ⌈(h−h')/8⌉ + ⌈h/(8d)⌉` (FIPS 205 §9). -/
def m (p : Params) : ℕ := p.digestBytes + p.treeIdxBytes + p.leafIdxBytes

/-- Signature size in bytes, `(1 + k(1+a) + h + d·len)·n` (FIPS 205 Fig 17). -/
def signatureBytes (p : Params) : ℕ := (1 + p.k * (1 + p.a) + p.h + p.d * p.len) * p.n

/-- Public-key size in bytes, `2n` (`PK.seed ‖ PK.root`). -/
def publicKeyBytes (p : Params) : ℕ := 2 * p.n

/-- Secret-key size in bytes, `4n` (`SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root`). -/
def secretKeyBytes (p : Params) : ℕ := 4 * p.n

end Params

/-- Raw SLH-DSA parameters paired with a proof of their mathematical validity.

Generic multi-layer algorithms should accept this bundle instead of accepting a bare `Params`.
There is deliberately no coercion back to `Params`: consumers must project `.params`, making the
point at which a validity proof is discarded visible. -/
structure ValidatedParams where
  /-- The executable arithmetic parameters. -/
  params : Params
  /-- Evidence that the arithmetic parameters are well formed. -/
  valid : params.Valid

namespace Params

/-- Check raw arithmetic parameters and package them with the resulting validity proof. -/
def validate (p : Params) : Option ValidatedParams :=
  if h : p.Valid then some ⟨p, h⟩ else none

@[simp]
theorem validate_eq_none_iff (p : Params) : p.validate = none ↔ ¬p.Valid := by
  simp [validate]

@[simp]
theorem validate_isSome_iff (p : Params) : p.validate.isSome = true ↔ p.Valid := by
  simp [validate]

end Params

/-- Hash families approved for SLH-DSA by FIPS 205. -/
inductive HashFamily where
  | sha2
  | shake
deriving Repr, DecidableEq, BEq

/-- The twelve approved parameter-set names from FIPS 205, Table 2. -/
inductive FipsParameterSet where
  | SLHDSA_SHA2_128s
  | SLHDSA_SHA2_128f
  | SLHDSA_SHA2_192s
  | SLHDSA_SHA2_192f
  | SLHDSA_SHA2_256s
  | SLHDSA_SHA2_256f
  | SLHDSA_SHAKE_128s
  | SLHDSA_SHAKE_128f
  | SLHDSA_SHAKE_192s
  | SLHDSA_SHAKE_192f
  | SLHDSA_SHAKE_256s
  | SLHDSA_SHAKE_256f
deriving Repr, DecidableEq, BEq

/-- Reference byte lengths fixed by the FIPS 205 parameter-set table. -/
structure FipsExpectedSizes where
  /-- Output length of `H_msg`. -/
  digest : ℕ
  /-- Encoded public-key length. -/
  publicKey : ℕ
  /-- Encoded secret-key length. -/
  secretKey : ℕ
  /-- Encoded signature length. -/
  signature : ℕ
deriving Repr, DecidableEq, BEq

namespace FipsParameterSet

/-- All FIPS 205 parameter sets in family-major order, with SHA2 followed by SHAKE. -/
def all : List FipsParameterSet :=
  [.SLHDSA_SHA2_128s, .SLHDSA_SHA2_128f, .SLHDSA_SHA2_192s, .SLHDSA_SHA2_192f,
    .SLHDSA_SHA2_256s, .SLHDSA_SHA2_256f, .SLHDSA_SHAKE_128s, .SLHDSA_SHAKE_128f,
    .SLHDSA_SHAKE_192s, .SLHDSA_SHAKE_192f, .SLHDSA_SHAKE_256s, .SLHDSA_SHAKE_256f]

/-- The exact standardized spelling of a FIPS 205 parameter-set name. -/
def name : FipsParameterSet → String
  | .SLHDSA_SHA2_128s => "SLH-DSA-SHA2-128s"
  | .SLHDSA_SHA2_128f => "SLH-DSA-SHA2-128f"
  | .SLHDSA_SHA2_192s => "SLH-DSA-SHA2-192s"
  | .SLHDSA_SHA2_192f => "SLH-DSA-SHA2-192f"
  | .SLHDSA_SHA2_256s => "SLH-DSA-SHA2-256s"
  | .SLHDSA_SHA2_256f => "SLH-DSA-SHA2-256f"
  | .SLHDSA_SHAKE_128s => "SLH-DSA-SHAKE-128s"
  | .SLHDSA_SHAKE_128f => "SLH-DSA-SHAKE-128f"
  | .SLHDSA_SHAKE_192s => "SLH-DSA-SHAKE-192s"
  | .SLHDSA_SHAKE_192f => "SLH-DSA-SHAKE-192f"
  | .SLHDSA_SHAKE_256s => "SLH-DSA-SHAKE-256s"
  | .SLHDSA_SHAKE_256f => "SLH-DSA-SHAKE-256f"

/-- The hash family selected by a FIPS 205 parameter set. -/
def hashFamily : FipsParameterSet → HashFamily
  | .SLHDSA_SHA2_128s | .SLHDSA_SHA2_128f | .SLHDSA_SHA2_192s | .SLHDSA_SHA2_192f
  | .SLHDSA_SHA2_256s | .SLHDSA_SHA2_256f => .sha2
  | .SLHDSA_SHAKE_128s | .SLHDSA_SHAKE_128f | .SLHDSA_SHAKE_192s | .SLHDSA_SHAKE_192f
  | .SLHDSA_SHAKE_256s | .SLHDSA_SHAKE_256f => .shake

/-- Interpret a FIPS 205 parameter-set name as its exact arithmetic parameters. -/
def params : FipsParameterSet → Params
  | .SLHDSA_SHA2_128s | .SLHDSA_SHAKE_128s =>
      { n := 16, h := 63, d := 7, hp := 9, a := 12, k := 14, lgw := 4 }
  | .SLHDSA_SHA2_128f | .SLHDSA_SHAKE_128f =>
      { n := 16, h := 66, d := 22, hp := 3, a := 6, k := 33, lgw := 4 }
  | .SLHDSA_SHA2_192s | .SLHDSA_SHAKE_192s =>
      { n := 24, h := 63, d := 7, hp := 9, a := 14, k := 17, lgw := 4 }
  | .SLHDSA_SHA2_192f | .SLHDSA_SHAKE_192f =>
      { n := 24, h := 66, d := 22, hp := 3, a := 8, k := 33, lgw := 4 }
  | .SLHDSA_SHA2_256s | .SLHDSA_SHAKE_256s =>
      { n := 32, h := 64, d := 8, hp := 8, a := 14, k := 22, lgw := 4 }
  | .SLHDSA_SHA2_256f | .SLHDSA_SHAKE_256f =>
      { n := 32, h := 68, d := 17, hp := 4, a := 9, k := 35, lgw := 4 }

/-- Reference sizes from FIPS 205, rather than values recomputed from `params`. -/
def expectedSizes : FipsParameterSet → FipsExpectedSizes
  | .SLHDSA_SHA2_128s | .SLHDSA_SHAKE_128s =>
      { digest := 30, publicKey := 32, secretKey := 64, signature := 7856 }
  | .SLHDSA_SHA2_128f | .SLHDSA_SHAKE_128f =>
      { digest := 34, publicKey := 32, secretKey := 64, signature := 17088 }
  | .SLHDSA_SHA2_192s | .SLHDSA_SHAKE_192s =>
      { digest := 39, publicKey := 48, secretKey := 96, signature := 16224 }
  | .SLHDSA_SHA2_192f | .SLHDSA_SHAKE_192f =>
      { digest := 42, publicKey := 48, secretKey := 96, signature := 35664 }
  | .SLHDSA_SHA2_256s | .SLHDSA_SHAKE_256s =>
      { digest := 47, publicKey := 64, secretKey := 128, signature := 29792 }
  | .SLHDSA_SHA2_256f | .SLHDSA_SHAKE_256f =>
      { digest := 49, publicKey := 64, secretKey := 128, signature := 49856 }

/-- Every named FIPS 205 parameter set has mathematically valid arithmetic parameters. -/
theorem params_valid (ps : FipsParameterSet) : ps.params.Valid := by
  cases ps <;> decide

/-- A FIPS 205 parameter set packaged for generic algorithms that require validity. -/
def validatedParams (ps : FipsParameterSet) : ValidatedParams :=
  ⟨ps.params, ps.params_valid⟩

/-- Derived digest, key, and signature sizes agree with the independent FIPS table constants. -/
theorem derived_sizes_eq_expected (ps : FipsParameterSet) :
    ps.params.m = ps.expectedSizes.digest ∧
    ps.params.publicKeyBytes = ps.expectedSizes.publicKey ∧
    ps.params.secretKeyBytes = ps.expectedSizes.secretKey ∧
    ps.params.signatureBytes = ps.expectedSizes.signature := by
  cases ps <;> decide

/-- `all` contains every FIPS 205 parameter set. -/
@[simp]
theorem mem_all (ps : FipsParameterSet) : ps ∈ all := by
  cases ps <;> simp [all]

/-- `all` contains no duplicate parameter-set name. -/
theorem all_nodup : all.Nodup := by
  decide

end FipsParameterSet

/-- Recognize the arithmetic shapes underlying FIPS 205 parameter sets.

The raw record does not encode the hash family, so a SHA2 set and the corresponding SHAKE set
have the same `Params` value. -/
def Params.IsFipsShape (p : Params) : Prop :=
  ∃ ps : FipsParameterSet, ps.params = p

/-- Nonstandard limited-use SLH-DSA profiles that are not FIPS 205 parameter sets. -/
inductive LimitedParameterSet where
  | SLHDSA_SHA2_128_24
deriving Repr, DecidableEq

namespace LimitedParameterSet

/-- Interpret a limited-use profile as its arithmetic parameters. -/
def params : LimitedParameterSet → Params
  | .SLHDSA_SHA2_128_24 => { n := 16, h := 22, d := 1, hp := 22, a := 24, k := 6, lgw := 2 }

/-- Every named limited-use profile has mathematically valid arithmetic parameters. -/
theorem params_valid (ps : LimitedParameterSet) : ps.params.Valid := by
  cases ps
  decide

/-- A limited-use profile packaged for generic algorithms that require validity. -/
def validatedParams (ps : LimitedParameterSet) : ValidatedParams :=
  ⟨ps.params, ps.params_valid⟩

end LimitedParameterSet

/-- The SLH-DSA-SHA2-128-24 parameter record (NIST SP 800-230 reduced set). -/
def slhdsaSha2_128_24 : Params := LimitedParameterSet.params .SLHDSA_SHA2_128_24

/-- Recognize the named limited-use parameter profiles. -/
def Params.IsLimited (p : Params) : Prop := p = slhdsaSha2_128_24

end SLHDSA

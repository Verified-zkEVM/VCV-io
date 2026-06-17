/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/
import Mathlib.Data.Nat.Log
import VCVio.OracleComp.Constructions.SampleableType

/-!
# SLH-DSA Parameters

Fixed constants and the named parameter sets for SLH-DSA (SPHINCS+, FIPS 205). The development
stays generic over the variable parameters while exposing the named instantiation we target
first, **SLH-DSA-SHA2-128-24** (the NIST SP 800-230 reduced parameter set:
`n=16, h=22, d=1, h'=22, a=24, k=6, w=4`).

The Winternitz and FORS lengths are derived from the primary parameters exactly as in FIPS 205
§5 (Eqs 5.1–5.3) and §9 (the message-digest length `m`); see `Params.len1`, `Params.len2`,
`Params.len`, and `Params.m`.

## References

- NIST FIPS 205 (SLH-DSA), Sections 4, 5, 9, 10, 11 (Table 2 parameter sets)
- NIST SP 800-230 ipd (the reduced 2²⁴-usage parameter set)
-/


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

/-- The named SLH-DSA parameter sets supported here. Currently only the SHA-2 128-24 reduced
set; SHAKE / 192 / 256 / C-series variants are future additions. -/
inductive ParameterSet where
  | SLHDSA_SHA2_128_24
deriving Repr, DecidableEq

namespace ParameterSet

/-- Interpret a named parameter set as the corresponding parameter record. -/
def params : ParameterSet → Params
  | .SLHDSA_SHA2_128_24 => { n := 16, h := 22, d := 1, hp := 22, a := 24, k := 6, lgw := 2 }

end ParameterSet

/-- The SLH-DSA-SHA2-128-24 parameter record (NIST SP 800-230 reduced set). -/
def slhdsaSha2_128_24 : Params := ParameterSet.params .SLHDSA_SHA2_128_24

/-- Recognize the parameter sets supported by this development. -/
def Params.isApproved (p : Params) : Prop := p = slhdsaSha2_128_24

end SLHDSA

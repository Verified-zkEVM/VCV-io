/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Signature
import LatticeCrypto.MLDSA.Concrete.Instance
import LatticeCrypto.MLDSA.Concrete.FFI

/-!
# ML-DSA Test Helpers

Shared test infrastructure: pass/fail counter, hex formatting, and FIPS 204 serialization
helpers used by the ML-DSA test suite.
-/


open MLDSA MLDSA.Concrete

namespace MLDSA.Test

/-! ## Test harness -/

/-- Mutable pass/fail counters for the ML-DSA test suite. -/
structure TestState where
  passed : Nat := 0
  failed : Nat := 0

/-- Record and print the result of a single ML-DSA test assertion. -/
def check (ref : IO.Ref TestState) (name : String) (ok : Bool)
    (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"  ✓ {name}"
    ref.modify fun s => { s with passed := s.passed + 1 }
  else
    IO.println s!"  ✗ {name} {detail}"
    ref.modify fun s => { s with failed := s.failed + 1 }

/-! ## Hex formatting -/

/-- Render a byte as two lowercase hexadecimal characters. -/
def hexByte (b : UInt8) : String :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  let c (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [c hi, c lo]

/-- Render the prefix of a byte array in hexadecimal for debugging output. -/
def toHex (ba : ByteArray) (maxBytes : Nat := 8) : String :=
  let pfx := Id.run do
    let mut parts : Array String := Array.mkEmpty (min ba.size maxBytes)
    for i in [:min ba.size maxBytes] do
      parts := parts.push (hexByte (ba[i]!))
    return String.join parts.toList
  pfx ++ if ba.size > maxBytes then "…" else ""

/-- Parse an even-length hexadecimal string into a byte array. -/
def parseHex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut out := ByteArray.empty
  let mut i := 0
  while i + 1 < chars.size do
    let hi := hexVal (chars.getD i ' ')
    let lo := hexVal (chars.getD (i + 1) ' ')
    out := out.push (hi * 16 + lo).toUInt8
    i := i + 2
  return out
where
  hexVal (c : Char) : Nat :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else 0

/-! ## FIPS 204 serialization (ML-DSA-65) -/

/-- Serialize an ML-DSA-65 public key with the concrete encoding bundle. -/
def serializePK65 (pk : PublicKey mldsa65 mldsa65Primitives) : ByteArray :=
  let enc := mldsa65Encoding
  enc.pkEncode pk.rho pk.t1

/-- Serialize an ML-DSA-65 secret key with the concrete encoding bundle. -/
def serializeSK65 (sk : SecretKey mldsa65) : ByteArray :=
  let enc := mldsa65Encoding
  enc.skEncode sk.rho sk.key sk.tr sk.s1 sk.s2 sk.t0

/-- Serialize an ML-DSA-65 signature with the concrete encoding bundle. -/
def serializeSig65 (sig : FIPSSignature mldsa65 mldsa65Primitives) : ByteArray :=
  let enc := mldsa65Encoding
  enc.sigEncode sig.cTilde sig.z sig.h

end MLDSA.Test

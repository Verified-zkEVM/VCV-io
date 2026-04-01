/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Internal
import LatticeCrypto.MLKEM.Concrete.Instance

/-!
# ML-KEM Test Helpers

Shared test infrastructure: pass/fail counter, hex formatting, and FIPS 203 serialization
helpers used by the ML-KEM test suite.
-/


open MLKEM MLKEM.Concrete

/-- Decidable equality for ML-KEM-768 encoded `u` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)
/-- Decidable equality for ML-KEM-768 encoded `v` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)
/-- Decidable equality for ML-KEM-512 encoded `u` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem512Encoding).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)
/-- Decidable equality for ML-KEM-512 encoded `v` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem512Encoding).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)
/-- Decidable equality for ML-KEM-1024 encoded `u` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem1024Encoding).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)
/-- Decidable equality for ML-KEM-1024 encoded `v` components. -/
instance : DecidableEq (MLKEM.Concrete.mlkem1024Encoding).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)

namespace MLKEM.Test

/-! ## Test harness -/

/-- Mutable pass/fail counters for the ML-KEM test suite. -/
structure TestState where
  passed : Nat := 0
  failed : Nat := 0

/-- Record and print the result of a single ML-KEM test assertion. -/
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
    for i in [0:min ba.size maxBytes] do
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

/-! ## Conversion helpers -/

/-- Convert a fixed-length byte vector into a `ByteArray`. -/
def vecToBA {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

/-! ## FIPS 203 serialization -/

/-- Serialize an ML-KEM-768 encapsulation key. -/
def serializeEK (ek : KPKE.PublicKey mlkem768 mlkem768Encoding) : ByteArray :=
  let t : ByteArray := ek.tHatEncoded
  t ++ vecToBA ek.rho

/-- Serialize an ML-KEM-768 decapsulation key. -/
def serializeDK (dk : DecapsulationKey mlkem768 mlkem768Encoding) : ByteArray :=
  let s : ByteArray := dk.dkPKE.sHatEncoded
  s ++ serializeEK dk.ekPKE ++ vecToBA dk.ekHash ++ vecToBA dk.z

/-- Serialize an ML-KEM-768 ciphertext. -/
def serializeCT (ct : KPKE.Ciphertext mlkem768 mlkem768Encoding) : ByteArray :=
  let u : ByteArray := ct.uEncoded
  let v : ByteArray := ct.vEncoded
  u ++ v

/-! ## FIPS 203 serialization (ML-KEM-512) -/

/-- Serialize an ML-KEM-512 encapsulation key. -/
def serializeEK512 (ek : KPKE.PublicKey mlkem512 mlkem512Encoding) : ByteArray :=
  let t : ByteArray := ek.tHatEncoded
  t ++ vecToBA ek.rho

/-- Serialize an ML-KEM-512 decapsulation key. -/
def serializeDK512 (dk : DecapsulationKey mlkem512 mlkem512Encoding) : ByteArray :=
  let s : ByteArray := dk.dkPKE.sHatEncoded
  s ++ serializeEK512 dk.ekPKE ++ vecToBA dk.ekHash ++ vecToBA dk.z

/-- Serialize an ML-KEM-512 ciphertext. -/
def serializeCT512 (ct : KPKE.Ciphertext mlkem512 mlkem512Encoding) : ByteArray :=
  let u : ByteArray := ct.uEncoded
  let v : ByteArray := ct.vEncoded
  u ++ v

/-! ## FIPS 203 serialization (ML-KEM-1024) -/

/-- Serialize an ML-KEM-1024 encapsulation key. -/
def serializeEK1024 (ek : KPKE.PublicKey mlkem1024 mlkem1024Encoding) : ByteArray :=
  let t : ByteArray := ek.tHatEncoded
  t ++ vecToBA ek.rho

/-- Serialize an ML-KEM-1024 decapsulation key. -/
def serializeDK1024 (dk : DecapsulationKey mlkem1024 mlkem1024Encoding) : ByteArray :=
  let s : ByteArray := dk.dkPKE.sHatEncoded
  s ++ serializeEK1024 dk.ekPKE ++ vecToBA dk.ekHash ++ vecToBA dk.z

/-- Serialize an ML-KEM-1024 ciphertext. -/
def serializeCT1024 (ct : KPKE.Ciphertext mlkem1024 mlkem1024Encoding) : ByteArray :=
  let u : ByteArray := ct.uEncoded
  let v : ByteArray := ct.vEncoded
  u ++ v

end MLKEM.Test

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Internal
import Examples.MLKEM.Concrete.Instance

/-!
# ML-KEM Test Helpers

Shared test infrastructure: pass/fail counter, hex formatting, and FIPS 203 serialization
helpers used by the ML-KEM test suite.
-/

set_option autoImplicit false

open MLKEM MLKEM.Concrete

instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)
instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)

namespace VCVioTest.MLKEM

/-! ## Test harness -/

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

def check (ref : IO.Ref TestState) (name : String) (ok : Bool)
    (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"  ✓ {name}"
    ref.modify fun s => { s with passed := s.passed + 1 }
  else
    IO.println s!"  ✗ {name} {detail}"
    ref.modify fun s => { s with failed := s.failed + 1 }

/-! ## Hex formatting -/

def hexByte (b : UInt8) : String :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  let c (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.mk [c hi, c lo]

def toHex (ba : ByteArray) (maxBytes : Nat := 8) : String :=
  let pfx := Id.run do
    let mut parts : Array String := Array.mkEmpty (min ba.size maxBytes)
    for i in [0:min ba.size maxBytes] do
      parts := parts.push (hexByte (ba[i]!))
    return String.join parts.toList
  pfx ++ if ba.size > maxBytes then "…" else ""

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

def vecToBA {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

/-! ## FIPS 203 serialization -/

def serializeEK (ek : KPKE.PublicKey mlkem768 mlkem768Encoding) : ByteArray :=
  let t : ByteArray := ek.tHatEncoded
  t ++ vecToBA ek.rho

def serializeDK (dk : DecapsulationKey mlkem768 mlkem768Encoding) : ByteArray :=
  let s : ByteArray := dk.dkPKE.sHatEncoded
  s ++ serializeEK dk.ekPKE ++ vecToBA dk.ekHash ++ vecToBA dk.z

def serializeCT (ct : KPKE.Ciphertext mlkem768 mlkem768Encoding) : ByteArray :=
  let u : ByteArray := ct.uEncoded
  let v : ByteArray := ct.vEncoded
  u ++ v

/-! ## Schoolbook multiplication (reference for NTT tests) -/

def schoolbookMul (f g : Rq) : Rq := Id.run do
  let fa := f.toArray
  let ga := g.toArray
  let mut h : Array Coeff := Array.replicate 256 0
  for i in [0:256] do
    for j in [0:256] do
      let fi := fa.getD i 0
      let gj := ga.getD j 0
      let k := (i + j) % 256
      if i + j < 256 then
        h := h.set! k ((h.getD k 0) + fi * gj)
      else
        h := h.set! k ((h.getD k 0) - fi * gj)
  Vector.ofFn fun ⟨i, _⟩ => h.getD i 0

end VCVioTest.MLKEM

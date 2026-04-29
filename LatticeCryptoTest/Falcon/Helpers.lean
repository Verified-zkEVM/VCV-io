/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Falcon.Concrete.Instance
import LatticeCrypto.Falcon.Concrete.FFI
import LatticeCrypto.Falcon.Concrete.FPR
import LatticeCrypto.Falcon.Concrete.SamplerZ
import LatticeCrypto.Falcon.Concrete.FloatLike
import LatticeCrypto.Falcon.Concrete.FFT
import LatticeCrypto.Falcon.Concrete.BigInt31
import LatticeCrypto.Falcon.Concrete.SmallPrimeNTT
import LatticeCrypto.Falcon.Concrete.FXR
import LatticeCrypto.Falcon.Concrete.Sign

/-!
# Falcon Test Helpers

Shared test infrastructure: pass/fail counter, hex formatting, and utility
functions used by the Falcon test suite.
-/


namespace Falcon.Test

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
  let c (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)
  String.ofList [c hi, c lo]

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

/-! ## ByteArray / Vector conversion -/

def vectorToByteArray {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

def byteArrayToVector (ba : ByteArray) (offset len : Nat) :
    Vector UInt8 len :=
  Vector.ofFn fun ⟨i, _⟩ =>
    let idx := offset + i
    if h : idx < ba.size then ba[idx] else 0

/-! ## Approximate comparison helpers -/

def checkFloat (ref : IO.Ref TestState) (name : String)
    (got expected : Float) (tol : Float := 0.0) : IO Unit := do
  let diff := Float.abs (got - expected)
  check ref name (diff ≤ tol) s!"got={got} exp={expected} diff={diff}"

def checkApproxU64 (ref : IO.Ref TestState) (name : String)
    (got expected : UInt64) (tol : Nat := 0) : IO Unit := do
  let diff := if got ≥ expected then (got - expected).toNat else (expected - got).toNat
  check ref name (diff ≤ tol) s!"got=0x{hexU64 got} exp=0x{hexU64 expected} diff={diff}"
where
  hexU64 (v : UInt64) : String := Id.run do
    let mut s := ""
    for i in [0:16] do
      let nibble := ((v >>> ((15 - i) * 4).toUInt64) &&& 0xF).toNat
      s := s ++ (if nibble < 10 then String.ofList [Char.ofNat (48 + nibble)]
        else String.ofList [Char.ofNat (55 + nibble)])
    return s

/-! ## Secret key decoding -/

def nbitsFG (logn : Nat) : Nat :=
  if logn ≥ 10 then 5 else if logn ≥ 8 then 6 else if logn ≥ 6 then 7 else 8

def trimI8Decode (data : ByteArray) (offset n nbits : Nat) :
    Option (Array Int32) := Id.run do
  let needed := (nbits * n) / 8
  let mask1 : UInt32 := ((1 : UInt32) <<< nbits.toUInt32) - 1
  let mask2 : UInt32 := (1 : UInt32) <<< (nbits.toUInt32 - 1)
  let mut acc : UInt32 := 0
  let mut accLen : Nat := 0
  let mut result : Array Int32 := Array.mkEmpty n
  for i in [0:needed] do
    let idx := offset + i
    let byte : UInt32 := if idx < data.size then data[idx]!.toUInt32 else 0
    acc := (acc <<< (8 : UInt32)) ||| byte
    accLen := accLen + 8
    for _ in [0:3] do
      if accLen ≥ nbits then
        accLen := accLen - nbits
        let w := (acc >>> accLen.toUInt32) &&& mask1
        let signExtended := w ||| ((0 : UInt32) - (w &&& mask2))
        if signExtended == (0 : UInt32) - mask2 then
          return none
        result := result.push signExtended.toInt32
  if result.size ≠ n then return none
  return some result

def decodeSecretKey (logn : Nat) (sk : ByteArray) :
    Option (Array Int32 × Array Int32 × Array Int32) := Id.run do
  let n := 1 <<< logn
  let nbits := nbitsFG logn
  let mut off := 1
  match trimI8Decode sk off n nbits with
  | none => return none
  | some f =>
    off := off + (n * nbits) / 8
    match trimI8Decode sk off n nbits with
    | none => return none
    | some g =>
      off := off + (n * nbits) / 8
      match trimI8Decode sk off n 8 with
      | none => return none
      | some capF => return some (f, g, capF)

/-! ## Coefficient conversions for G computation -/

def int32ToCoeff (v : Int32) : Falcon.Coeff :=
  let u := v.toUInt32.toNat
  if u < 0x80000000 then (u : Falcon.Coeff)
  else (0 : Falcon.Coeff) - ((0x100000000 - u : Nat) : Falcon.Coeff)

def coeffToInt32 (c : Falcon.Coeff) : Int32 :=
  if c.val > Falcon.modulus / 2 then
    (0 : Int32) - ((Falcon.modulus - c.val).toUInt32.toInt32)
  else c.val.toUInt32.toInt32

def computeCapG512 (capF : Array Int32) (pk : ByteArray) :
    Option (Array Int32) :=
  match Falcon.Concrete.pkDecode 512 (pk.extract 1 pk.size) with
  | none => none
  | some h =>
    let capFRq : Falcon.Rq 512 := Vector.ofFn fun ⟨i, _⟩ =>
      int32ToCoeff (capF.getD i 0)
    let capGRq := Falcon.Concrete.invNTT 9 (Falcon.Concrete.multiplyNTTs
      (Falcon.Concrete.ntt 9 h) (Falcon.Concrete.ntt 9 capFRq))
    some (capGRq.toArray.map coeffToInt32)

def computeCapG1024 (capF : Array Int32) (pk : ByteArray) :
    Option (Array Int32) :=
  match Falcon.Concrete.pkDecode 1024 (pk.extract 1 pk.size) with
  | none => none
  | some h =>
    let capFRq : Falcon.Rq 1024 := Vector.ofFn fun ⟨i, _⟩ =>
      int32ToCoeff (capF.getD i 0)
    let capGRq := Falcon.Concrete.invNTT 10 (Falcon.Concrete.multiplyNTTs
      (Falcon.Concrete.ntt 10 h) (Falcon.Concrete.ntt 10 capFRq))
    some (capGRq.toArray.map coeffToInt32)

end Falcon.Test

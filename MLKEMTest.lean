/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Internal
import Examples.MLKEM.Concrete.Instance

/-!
# ML-KEM Test Runner

Tests the pure-Lean ML-KEM-768 implementation against the verified mlkem-native (v1.1.0) FFI.
Six test groups exercise SHA-3 primitives, NTT roundtrip, encoding roundtrip, and full
keygen / encaps / decaps byte-exact comparisons between the Lean spec and mlkem-native.

## How to run

```bash
git submodule update --init --recursive   # fetch mlkem-native
lake exe cache get                        # fetch Mathlib oleans
lake build mlkem_test                     # compile Lean + C FFI
.lake/build/bin/mlkem_test                # run
```
-/

set_option autoImplicit false

open MLKEM MLKEM.Concrete

instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedU :=
  inferInstanceAs (DecidableEq ByteArray)
instance : DecidableEq (MLKEM.Concrete.mlkem768Encoding).EncodedV :=
  inferInstanceAs (DecidableEq ByteArray)

/-! ## Helpers -/

private def vecToBA {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

private def hexByte (b : UInt8) : String :=
  let hi := b.toNat / 16
  let lo := b.toNat % 16
  let c (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [c hi, c lo]

private def toHex (ba : ByteArray) (maxBytes : Nat := 8) : String :=
  let n := min ba.size maxBytes
  let bytes := (List.range n).map fun i => hexByte (ba[i]!)
  String.join bytes ++ if ba.size > maxBytes then "…" else ""

/-! ## Serialization: Lean spec types → byte arrays (FIPS 203 wire format) -/

private def serializeEK (ek : KPKE.PublicKey mlkem768 mlkem768Encoding) : ByteArray :=
  let t : ByteArray := ek.tHatEncoded
  t ++ vecToBA ek.rho

private def serializeDK (dk : DecapsulationKey mlkem768 mlkem768Encoding) : ByteArray :=
  let s : ByteArray := dk.dkPKE.sHatEncoded
  s ++ serializeEK dk.ekPKE ++ vecToBA dk.ekHash ++ vecToBA dk.z

private def serializeCT (ct : KPKE.Ciphertext mlkem768 mlkem768Encoding) : ByteArray :=
  let u : ByteArray := ct.uEncoded
  let v : ByteArray := ct.vEncoded
  u ++ v

/-! ## Test harness -/

structure TestState where
  passed : Nat := 0
  failed : Nat := 0

private def check (ref : IO.Ref TestState) (name : String) (ok : Bool)
    (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"  ✓ {name}"
    ref.modify fun s => { s with passed := s.passed + 1 }
  else
    IO.println s!"  ✗ {name} {detail}"
    ref.modify fun s => { s with failed := s.failed + 1 }

def main : IO Unit := do
  let st ← IO.mkRef ({} : TestState)

  IO.println "=== ML-KEM-768 Correctness Tests ==="
  IO.println ""

  -- ── 1. SHA-3 sanity ──────────────────────────────────────
  IO.println "1. SHA-3 sanity"
  do
    let abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩
    let d256 := FFI.sha3_256 abc
    let exp256 : List UInt8 := [0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2]
    let act256 := (List.range 8).map fun i => d256[i]!
    check st "SHA3-256(\"abc\") first 8 bytes" (act256 == exp256)

    let d512 := FFI.sha3_512 abc
    let exp512 : List UInt8 := [0xb7, 0x51, 0x85, 0x0b, 0x1a, 0x57, 0x16, 0x8a]
    let act512 := (List.range 8).map fun i => d512[i]!
    check st "SHA3-512(\"abc\") first 8 bytes" (act512 == exp512)
  IO.println ""

  -- ── 2. NTT roundtrip ────────────────────────────────────
  IO.println "2. NTT roundtrip (invNTT ∘ NTT = id)"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let f' := MLKEM.Concrete.invNTT (MLKEM.Concrete.ntt f)
    check st "invNTT(NTT(0,1,…,255)) = (0,1,…,255)" (f == f')

    let g : Rq := Vector.ofFn fun _ => (42 : Coeff)
    let g' := MLKEM.Concrete.invNTT (MLKEM.Concrete.ntt g)
    check st "NTT roundtrip on constant poly" (g == g')
  IO.println ""

  -- ── 2b. NTT multiplication ────────────────────────────
  IO.println "2b. NTT multiplication (invNTT(mul(NTT f, NTT g)) = f*g mod X^256+1)"
  do
    let schoolbook (f g : Rq) : Rq := Id.run do
      let mut h : Array Coeff := Array.replicate 256 0
      for i in List.range 256 do
        for j in List.range 256 do
          let fi := f.toArray.getD i 0
          let gj := g.toArray.getD j 0
          let k := (i + j) % 256
          if i + j < 256 then
            h := h.set! k ((h.getD k 0) + fi * gj)
          else
            h := h.set! k ((h.getD k 0) - fi * gj)
      Vector.ofFn fun ⟨i, _⟩ => h.getD i 0

    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => if i < 3 then (1 : Coeff) else 0
    let g : Rq := Vector.ofFn fun ⟨i, _⟩ => if i == 0 then (1 : Coeff) else if i == 1 then 2 else 0
    let expected := schoolbook f g
    let nttResult := MLKEM.Concrete.invNTT
      (MLKEM.Concrete.multiplyNTTs (MLKEM.Concrete.ntt f) (MLKEM.Concrete.ntt g))
    check st "NTT mul: (1+X+X²)*(1+2X)" (nttResult == expected)
      s!"NTT=[{(nttResult.toArray.toList.take 6).map (·.val)}] expected=[{(expected.toArray.toList.take 6).map (·.val)}]"

    let f2 : Rq := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let g2 : Rq := Vector.ofFn fun ⟨i, _⟩ => ((256 - i) % modulus : Nat)
    let expected2 := schoolbook f2 g2
    let nttResult2 := MLKEM.Concrete.invNTT
      (MLKEM.Concrete.multiplyNTTs (MLKEM.Concrete.ntt f2) (MLKEM.Concrete.ntt g2))
    check st "NTT mul: (0,1,…,255)*(256,255,…,1)" (nttResult2 == expected2)
  IO.println ""

  -- ── 3. ByteEncode / ByteDecode roundtrip ────────────────
  IO.println "3. ByteEncode / ByteDecode roundtrip"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => ((i * 13 % modulus : Nat) : Coeff)
    let decoded := byteDecode 12 (byteEncode 12 f)
    check st "ByteDecode_12(ByteEncode_12(f)) = f" (f == decoded)

    let g : Rq := Vector.ofFn fun ⟨i, _⟩ => ((i % 16 : Nat) : Coeff)
    let dec4 := byteDecode 4 (byteEncode 4 g)
    check st "ByteDecode_4(ByteEncode_4(g)) = g" (g == dec4)
  IO.println ""

  -- ── 4. Full keygen: Lean spec vs mlkem-native ───────────
  IO.println "4. Full ML-KEM-768 keygen: Lean spec vs mlkem-native"
  do
    let d : Seed32 := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let z : Seed32 := Vector.ofFn fun ⟨i, _⟩ => (32 + i).toUInt8
    let coins64 := vecToBA d ++ vecToBA z

    let (ekRef, dkRef) := FFI.mlkemKeypairDerand coins64
    check st "mlkem-native keygen sizes" (ekRef.size == 1184 && dkRef.size == 2400)

    let (ekLean, dkLean) := keygenInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives d z
    let ekB := serializeEK ekLean
    let dkB := serializeDK dkLean

    check st "Lean ek size = 1184" (ekB.size == 1184)
    check st "Lean dk size = 2400" (dkB.size == 2400)

    let ekMatch := ekB == ekRef
    check st "ek: Lean spec = mlkem-native" ekMatch
      s!"Lean={toHex ekB} ref={toHex ekRef}"
    if !ekMatch then
      let mut first := ekB.size
      for i in List.range (min ekB.size ekRef.size) do
        if ekB[i]! != ekRef[i]! && first == ekB.size then
          first := i
      IO.println s!"    first diff at byte {first} (Lean={hexByte (ekB[first]!)}, ref={hexByte (ekRef[first]!)})"
      IO.println s!"    byte {first} is in tHat[{first / 384}], coeff ~{(first % 384) * 8 / 12}"

    let dkMatch := dkB == dkRef
    check st "dk: Lean spec = mlkem-native" dkMatch
      s!"Lean={toHex dkB} ref={toHex dkRef}"
    if !dkMatch then
      let mut first := dkB.size
      for i in List.range (min dkB.size dkRef.size) do
        if dkB[i]! != dkRef[i]! && first == dkB.size then
          first := i
      IO.println s!"    first diff at byte {first} (Lean={hexByte (dkB[first]!)}, ref={hexByte (dkRef[first]!)})"
  IO.println ""

  -- ── 5. Full encaps + decaps: Lean spec vs mlkem-native ──
  IO.println "5. Full ML-KEM-768 encaps + decaps: Lean spec vs mlkem-native"
  do
    let d : Seed32 := Vector.ofFn fun _ => (0xAA : UInt8)
    let z : Seed32 := Vector.ofFn fun _ => (0xBB : UInt8)
    let coins64 := vecToBA d ++ vecToBA z

    let (ekRef, dkRef) := FFI.mlkemKeypairDerand coins64

    let (ekLean, dkLean) := keygenInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives d z

    let m : Message := Vector.ofFn fun _ => (0x55 : UInt8)

    let (ctRef, ssRef) := FFI.mlkemEncDerand ekRef (vecToBA m)
    check st "mlkem-native encaps sizes" (ctRef.size == 1088 && ssRef.size == 32)

    let (ssLean, ctLean) := encapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives ekLean m
    let ctB := serializeCT ctLean
    let ssB := vecToBA ssLean

    check st "ct: Lean spec = mlkem-native" (ctB == ctRef)
      s!"Lean={toHex ctB} ref={toHex ctRef}"
    check st "ss: Lean spec = mlkem-native" (ssB == ssRef)
      s!"Lean={toHex ssB} ref={toHex ssRef}"

    let ssDecRef := FFI.mlkemDec dkRef ctRef
    let ssDecLean := decapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives dkLean ctLean
    let ssDecB := vecToBA ssDecLean

    check st "decaps ss: Lean spec = mlkem-native" (ssDecB == ssDecRef)
      s!"Lean={toHex ssDecB} ref={toHex ssDecRef}"
    check st "decaps roundtrip: ss_enc = ss_dec" (ssB == ssDecB)
  IO.println ""

  -- ── 6. Second key pair (different coins) ────────────────
  IO.println "6. Second key pair (different coins)"
  do
    let d : Seed32 := Vector.ofFn fun ⟨i, _⟩ => (0xFF - i).toUInt8
    let z : Seed32 := Vector.ofFn fun ⟨i, _⟩ => (i * 7 % 256).toUInt8
    let coins64 := vecToBA d ++ vecToBA z

    let (ekRef, dkRef) := FFI.mlkemKeypairDerand coins64

    let (ekLean, dkLean) := keygenInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives d z
    let ekB := serializeEK ekLean
    let dkB := serializeDK dkLean

    check st "ek: Lean spec = mlkem-native (2nd)" (ekB == ekRef)
      s!"Lean={toHex ekB} ref={toHex ekRef}"
    check st "dk: Lean spec = mlkem-native (2nd)" (dkB == dkRef)
      s!"Lean={toHex dkB} ref={toHex dkRef}"

    let m : Message := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let (ctRef, ssRef) := FFI.mlkemEncDerand ekRef (vecToBA m)
    let (ssLean, ctLean) := encapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives ekLean m
    let ctB := serializeCT ctLean
    let ssB := vecToBA ssLean

    check st "ct: Lean spec = mlkem-native (2nd)" (ctB == ctRef)
      s!"Lean={toHex ctB} ref={toHex ctRef}"
    check st "ss: Lean spec = mlkem-native (2nd)" (ssB == ssRef)
      s!"Lean={toHex ssB} ref={toHex ssRef}"

    let ssDecRef := FFI.mlkemDec dkRef ctRef
    let ssDecLean := decapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives dkLean ctLean
    check st "decaps: Lean spec = mlkem-native (2nd)"
      (vecToBA ssDecLean == ssDecRef)

  IO.println ""
  let s ← st.get
  IO.println s!"=== {s.passed} passed, {s.failed} failed ==="
  if s.failed > 0 then
    IO.Process.exit 1

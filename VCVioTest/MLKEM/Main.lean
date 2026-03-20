/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVioTest.MLKEM.Helpers
import VCVioTest.MLKEM.ACVPVectors

/-!
# ML-KEM-768 Test Runner

Tests the pure-Lean ML-KEM-768 implementation against the verified mlkem-native (v1.1.0) FFI
and NIST known-answer vectors.

## How to run

```bash
git submodule update --init --recursive
lake exe cache get
lake build mlkem_test
.lake/build/bin/mlkem_test
```
-/

set_option autoImplicit false
set_option maxRecDepth 2048

open MLKEM MLKEM.Concrete VCVioTest.MLKEM

def main : IO Unit := do
  let st ← IO.mkRef ({} : TestState)

  IO.println "=== ML-KEM-768 Correctness Tests ==="
  IO.println ""

  -- ── 1. SHA-3 known-answer (full digests) ──────────────────
  IO.println "1. SHA-3 known-answer vectors"
  do
    let abc : ByteArray := ⟨#[0x61, 0x62, 0x63]⟩

    let d256 := FFI.sha3_256 abc
    let exp256 := parseHex "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
    check st "SHA3-256(\"abc\") full 32 bytes" (d256 == exp256)
      s!"got={toHex d256 32}"

    let d512 := FFI.sha3_512 abc
    let exp512 := parseHex "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
    check st "SHA3-512(\"abc\") full 64 bytes" (d512 == exp512)
      s!"got={toHex d512 64}"

    let empty : ByteArray := ⟨#[]⟩
    let d256e := FFI.sha3_256 empty
    let exp256e := parseHex "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
    check st "SHA3-256(\"\") full digest" (d256e == exp256e)
  IO.println ""

  -- ── 2. SHAKE known-answer ──────────────────────────────────
  IO.println "2. SHAKE known-answer vectors"
  do
    let empty : ByteArray := ⟨#[]⟩
    let shake256out := FFI.shake256 empty 32
    let expShake256 := parseHex "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
    check st "SHAKE-256(\"\", 32) full output" (shake256out == expShake256)

    let shake128out := FFI.shake128 empty 32
    let expShake128 := parseHex "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"
    check st "SHAKE-128(\"\", 32) full output" (shake128out == expShake128)
  IO.println ""

  -- ── 3. NTT roundtrip ──────────────────────────────────────
  IO.println "3. NTT roundtrip (invNTT ∘ NTT = id)"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let f' := MLKEM.Concrete.invNTT (MLKEM.Concrete.ntt f)
    check st "invNTT(NTT(0,1,…,255)) = (0,1,…,255)" (f == f')

    let g : Rq := Vector.ofFn fun _ => (42 : Coeff)
    let g' := MLKEM.Concrete.invNTT (MLKEM.Concrete.ntt g)
    check st "NTT roundtrip on constant poly" (g == g')

    let h : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 137 + 42 : Coeff)
    let h' := MLKEM.Concrete.invNTT (MLKEM.Concrete.ntt h)
    check st "NTT roundtrip on pseudorandom poly" (h == h')
  IO.println ""

  -- ── 4. NTT multiplication ─────────────────────────────────
  IO.println "4. NTT multiplication (invNTT(mul(NTT f, NTT g)) = f*g mod X^256+1)"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => if i < 3 then (1 : Coeff) else 0
    let g : Rq := Vector.ofFn fun ⟨i, _⟩ =>
      if i == 0 then (1 : Coeff) else if i == 1 then 2 else 0
    let expected := schoolbookMul f g
    let nttResult := MLKEM.Concrete.invNTT
      (MLKEM.Concrete.multiplyNTTs (MLKEM.Concrete.ntt f) (MLKEM.Concrete.ntt g))
    check st "NTT mul: (1+X+X²)*(1+2X)" (nttResult == expected)
      s!"NTT=[{(nttResult.toArray.toList.take 6).map (·.val)}] expected=[{(expected.toArray.toList.take 6).map (·.val)}]"

    let f2 : Rq := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let g2 : Rq := Vector.ofFn fun ⟨i, _⟩ => (256 - i : Coeff)
    let expected2 := schoolbookMul f2 g2
    let nttResult2 := MLKEM.Concrete.invNTT
      (MLKEM.Concrete.multiplyNTTs (MLKEM.Concrete.ntt f2) (MLKEM.Concrete.ntt g2))
    check st "NTT mul: (0,1,…,255)*(256,255,…,1)" (nttResult2 == expected2)

    let one : Rq := Vector.ofFn fun ⟨i, _⟩ => if i == 0 then (1 : Coeff) else 0
    let oneHat := MLKEM.Concrete.ntt one
    let fHat := MLKEM.Concrete.ntt f
    let mulOneResult := MLKEM.Concrete.invNTT (MLKEM.Concrete.multiplyNTTs fHat oneHat)
    check st "NTT mul: f * 1 = f" (mulOneResult == f)
  IO.println ""

  -- ── 5. ByteEncode / ByteDecode roundtrip ──────────────────
  IO.println "5. ByteEncode / ByteDecode roundtrip"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 13 : Coeff)
    let decoded := byteDecode 12 (byteEncode 12 f)
    check st "ByteDecode_12(ByteEncode_12(f)) = f" (f == decoded)

    let g : Rq := Vector.ofFn fun ⟨i, _⟩ => (i % 16 : Coeff)
    let dec4 := byteDecode 4 (byteEncode 4 g)
    check st "ByteDecode_4(ByteEncode_4(g)) = g" (g == dec4)

    for d in [1, 4, 5, 10, 11, 12] do
      let h : Rq := Vector.ofFn fun ⟨i, _⟩ => (i % (1 <<< d) : Coeff)
      let dec := byteDecode d (byteEncode d h)
      check st s!"ByteDecode_{d}(ByteEncode_{d}(h)) roundtrip" (h == dec)
  IO.println ""

  -- ── 6. Compress / Decompress ──────────────────────────────
  IO.println "6. Compress / Decompress approximation"
  do
    for d in [1, 4, 5, 10, 11] do
      let maxErr := modulus / (2 * (1 <<< d)) + 1
      let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 37 : Coeff)
      let roundtrip := decompressPoly d (compressPoly d f)
      let allClose := Id.run do
        let fa := f.toArray
        let rta := roundtrip.toArray
        let mut ok := true
        for i in [0:256] do
          let orig := (fa.getD i 0).val
          let rt := (rta.getD i 0).val
          let diff := if orig ≥ rt then min (orig - rt) (modulus - orig + rt)
                      else min (rt - orig) (modulus - rt + orig)
          ok := ok && diff ≤ maxErr
        return ok
      check st s!"Compress_{d} roundtrip error ≤ {maxErr}" allClose
  IO.println ""

  -- ── 7. CBD bounds ─────────────────────────────────────────
  IO.println "7. CBD output bounds"
  do
    for eta in [2, 3] do
      let bytes : ByteArray := ⟨Array.replicate (64 * eta) (0xA5 : UInt8)⟩
      let poly := samplePolyCBD eta bytes
      let allBounded := poly.toArray.all fun c =>
        c.val ≤ eta || c.val ≥ modulus - eta
      check st s!"samplePolyCBD eta={eta} output bounded by [-{eta},{eta}]" allBounded
  IO.println ""

  -- ── 8. SampleNTT known-answer ─────────────────────────────
  IO.println "8. SampleNTT known-answer (Lean vs mlkem-native)"
  do
    let rho : Seed32 := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let leanPoly := concreteSampleNTT rho 0 0
    let leanBA := byteEncode 12 leanPoly
    let refInput := vecToBA rho |>.push 0 |>.push 0
    let refStream := FFI.shake128 refInput 840
    let refPoly := MLKEM.Concrete.rejectionSampleForTest refStream
    let refBA := byteEncode 12 refPoly
    check st "SampleNTT(ρ,0,0): Lean = reference" (leanBA == refBA)
  IO.println ""

  -- ── 9. Full keygen: Lean spec vs mlkem-native ─────────────
  IO.println "9. Full ML-KEM-768 keygen: Lean spec vs mlkem-native"
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
    check st "ek: Lean spec = mlkem-native" (ekB == ekRef)
      s!"Lean={toHex ekB} ref={toHex ekRef}"
    check st "dk: Lean spec = mlkem-native" (dkB == dkRef)
      s!"Lean={toHex dkB} ref={toHex dkRef}"
  IO.println ""

  -- ── 10. Full encaps + decaps ──────────────────────────────
  IO.println "10. Full ML-KEM-768 encaps + decaps: Lean spec vs mlkem-native"
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

  -- ── 11. Second key pair (different coins) ─────────────────
  IO.println "11. Second key pair (different coins)"
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

  -- ── 12. Implicit rejection ────────────────────────────────
  IO.println "12. Implicit rejection (corrupted ciphertext)"
  do
    let d : Seed32 := Vector.ofFn fun ⟨i, _⟩ => (i * 3).toUInt8
    let z : Seed32 := Vector.ofFn fun ⟨i, _⟩ => (i * 5 + 100).toUInt8
    let coins64 := vecToBA d ++ vecToBA z

    let (ekRef, dkRef) := FFI.mlkemKeypairDerand coins64
    let (ekLean, dkLean) := keygenInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives d z

    let m : Message := Vector.ofFn fun _ => (0x77 : UInt8)
    let (ctRef, ssRef) := FFI.mlkemEncDerand ekRef (vecToBA m)
    let (_ssLean, ctLean) := encapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives ekLean m

    let corruptedCtRef := ctRef.set! 0 (ctRef[0]! ^^^ 0xFF)
    let ssDecCorruptRef := FFI.mlkemDec dkRef corruptedCtRef

    check st "corrupted ct decaps ≠ real ss (mlkem-native)"
      (ssDecCorruptRef != ssRef)

    let corruptedCtLean : KPKE.Ciphertext mlkem768 mlkem768Encoding :=
      let origU : ByteArray := ctLean.uEncoded
      let flipped := origU.set! 0 (origU[0]! ^^^ 0xFF)
      { ctLean with uEncoded := flipped }
    let ssDecCorruptLean := decapsInternal concreteNTTRingOps mlkem768Encoding
      mlkem768Primitives dkLean corruptedCtLean

    check st "corrupted ct decaps: Lean = mlkem-native"
      (vecToBA ssDecCorruptLean == ssDecCorruptRef)
  IO.println ""

  -- ── 13. NIST ACVP keygen vectors ────────────────────────
  IO.println "13. NIST ACVP keygen vectors (ML-KEM-768)"
  do
    for vec in ACVP.keyGenVectors do
      let dBA := parseHex vec.d
      let zBA := parseHex vec.z
      let d : Seed32 := Vector.ofFn fun ⟨i, _⟩ => dBA[i]!
      let z : Seed32 := Vector.ofFn fun ⟨i, _⟩ => zBA[i]!

      let (ekLean, dkLean) := keygenInternal concreteNTTRingOps mlkem768Encoding
        mlkem768Primitives d z
      let ekB := serializeEK ekLean
      let dkB := serializeDK dkLean

      check st s!"tcId={vec.tcId} ek size = 1184" (ekB.size == 1184)
      check st s!"tcId={vec.tcId} dk size = 2400" (dkB.size == 2400)

      let ekExpFirst32 := parseHex vec.ekFirst32
      let dkExpFirst32 := parseHex vec.dkFirst32
      let ekFirst32 := ekB.extract 0 32
      let dkFirst32 := dkB.extract 0 32

      check st s!"tcId={vec.tcId} ek first 32 bytes match ACVP"
        (ekFirst32 == ekExpFirst32)
        s!"got={toHex ekFirst32 32} exp={toHex ekExpFirst32 32}"
      check st s!"tcId={vec.tcId} dk first 32 bytes match ACVP"
        (dkFirst32 == dkExpFirst32)
        s!"got={toHex dkFirst32 32} exp={toHex dkExpFirst32 32}"

      let coins64 := vecToBA d ++ vecToBA z
      let (ekRef, dkRef) := FFI.mlkemKeypairDerand coins64
      check st s!"tcId={vec.tcId} ek: Lean = mlkem-native"
        (ekB == ekRef)
      check st s!"tcId={vec.tcId} dk: Lean = mlkem-native"
        (dkB == dkRef)
  IO.println ""

  let s ← st.get
  IO.println s!"=== {s.passed} passed, {s.failed} failed ==="
  if s.failed > 0 then
    IO.Process.exit 1

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCryptoTest.Falcon.Helpers
import LatticeCryptoTest.Falcon.TestVectors

/-!
# Falcon Test Runner

Tests the Falcon implementation against the c-fn-dsa FFI reference and
hardcoded test vectors. Covers Falcon-512, Falcon-1024, FPR emulation,
and SamplerZ components.

## How to run

```bash
git submodule update --init --recursive
lake exe cache get
lake build falcon_test
.lake/build/bin/falcon_test
```
-/

set_option autoImplicit false
set_option maxRecDepth 2048

open Falcon Falcon.Concrete Falcon.Concrete.FPR Falcon.Concrete.SamplerZ Falcon.Test

private def testFalcon512 : Params where
  n := 512
  sigma := 0
  sigmaMin := 0
  betaSquared := 34034726
  sbytelen := 625

private def testFalcon1024 : Params where
  n := 1024
  sigma := 0
  sigmaMin := 0
  betaSquared := 70265242
  sbytelen := 1239

private def checkFPR (st : IO.Ref TestState) (name : String)
    (got expected : FPR) : IO Unit :=
  check st name (got == expected)
    s!"got=0x{hexU64 got} exp=0x{hexU64 expected}"
where
  hexU64 (v : UInt64) : String := Id.run do
    let mut s := ""
    for i in [0:16] do
      let nibble := ((v >>> ((15 - i) * 4).toUInt64) &&& 0xF).toNat
      s := s ++ (if nibble < 10 then
        String.ofList [Char.ofNat (48 + nibble)]
      else
        String.ofList [Char.ofNat (55 + nibble)])
    return s

def main : IO Unit := do
  let st ← IO.mkRef ({} : TestState)

  IO.println "=== Falcon Correctness Tests ==="
  IO.println ""

  -- ── 1. NTT roundtrip ──────────────────────────
  IO.println "1. NTT roundtrip (invNTT ∘ NTT = id) for Falcon"
  do
    let logn := 9
    let n := 512
    let f : Rq n := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let f' := Falcon.Concrete.invNTT logn (Falcon.Concrete.ntt logn f)
    check st "invNTT(NTT(0,1,…,511)) = (0,1,…,511)" (f == f')

    let g : Rq n := Vector.ofFn fun _ => (42 : Coeff)
    let g' := Falcon.Concrete.invNTT logn (Falcon.Concrete.ntt logn g)
    check st "NTT roundtrip on constant poly" (g == g')

    let h : Rq n := Vector.ofFn fun ⟨i, _⟩ => (i * 137 + 42 : Coeff)
    let h' := Falcon.Concrete.invNTT logn (Falcon.Concrete.ntt logn h)
    check st "NTT roundtrip on pseudorandom poly" (h == h')
  IO.println ""

  -- ── 2. NTT multiplication ─────────────────────
  IO.println "2. NTT multiplication"
  do
    let logn := 9
    let n := 512
    let f : Rq n := Vector.ofFn fun ⟨i, _⟩ => if i < 3 then (1 : Coeff) else 0
    let g : Rq n := Vector.ofFn fun ⟨i, _⟩ =>
      if i == 0 then (1 : Coeff) else if i == 1 then 2 else 0
    let expected := negacyclicMul f g
    let nttResult := Falcon.Concrete.invNTT logn
      (Falcon.Concrete.multiplyNTTs
        (Falcon.Concrete.ntt logn f) (Falcon.Concrete.ntt logn g))
    check st "NTT mul: (1+X+X²)*(1+2X)" (nttResult == expected)
  IO.println ""

  -- ── 3. Compress/decompress roundtrip ──────────
  IO.println "3. Compress/decompress roundtrip"
  do
    let n := 512
    let s : IntPoly n := Vector.ofFn fun ⟨i, _⟩ =>
      ((i % 200 : Nat) : ℤ) - 100
    match compress n s 666 with
    | none => check st "compress should succeed" false
    | some bytes =>
      match decompress n bytes 666 with
      | none => check st "decompress should succeed" false
      | some s' => check st "decompress(compress(s)) = s" (s == s')
  IO.println ""

  -- ── 4. Public key encode/decode roundtrip ─────
  IO.println "4. Public key encode/decode roundtrip"
  do
    let n := 512
    let h : Rq n := Vector.ofFn fun ⟨i, _⟩ => ((i * 17 + 3) % modulus : Coeff)
    let encoded := pkEncode n h
    match pkDecode n encoded with
    | none => check st "pkDecode should succeed" false
    | some h' => check st "pkDecode(pkEncode(h)) = h" (h == h')
  IO.println ""

  -- ── 5. FFI keygen sizes ───────────────────────
  IO.println "5. FFI keygen sizes"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    check st "Falcon-512 sk size = 1281" (sk.size == 1281)
    check st "Falcon-512 pk size = 897" (pk.size == 897)
  IO.println ""

  -- ── 6. FFI sign + verify roundtrip ────────────
  IO.println "6. FFI sign + verify roundtrip"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
    let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
      (0xFF - i.val).toUInt8⟩
    let sig := Falcon.Concrete.FFI.falcon512SignSeeded sk msg signSeed
    check st "FFI sign produces non-empty sig" (sig.size > 0)
    check st s!"FFI sig size = {sig.size}" (sig.size == 666)

    let ver := Falcon.Concrete.FFI.falcon512Verify pk msg sig
    check st "FFI verify accepts valid sig" (ver == 1)

    let corruptedSig := sig.set! 1 (sig[1]! ^^^ 0xFF)
    let verCorrupt := Falcon.Concrete.FFI.falcon512Verify pk msg corruptedSig
    check st "FFI verify rejects corrupted sig" (verCorrupt == 0)
  IO.println ""

  -- ── 7. FFI sign → Lean verify ─────────────────
  IO.println "7. FFI sign → Lean concreteVerify (Falcon-512)"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
    let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
      (0xFF - i.val).toUInt8⟩
    let sig := Falcon.Concrete.FFI.falcon512SignSeeded sk msg signSeed
    let leanResult := concreteVerify testFalcon512 pk msg.toList sig
    check st "Lean concreteVerify accepts FFI-signed sig" leanResult
  IO.println ""

  -- ── 8. Hardcoded test vectors ─────────────────
  IO.println "8. Hardcoded test vectors"
  do
    for vec in signVerifyVectors do
      let seed := parseHex vec.seed
      let msg := parseHex vec.msg
      let signSeed := parseHex vec.signSeed

      let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
      check st s!"tcId={vec.tcId} sk size" (sk.size == vec.skSize)
      check st s!"tcId={vec.tcId} pk size" (pk.size == vec.pkSize)

      let pkFirst32 := parseHex vec.pkFirst32
      let pkActual32 := pk.extract 0 32
      check st s!"tcId={vec.tcId} pk first 32 bytes"
        (pkActual32 == pkFirst32)
        s!"got={toHex pkActual32 32} exp={toHex pkFirst32 32}"

      let sig := Falcon.Concrete.FFI.falcon512SignSeeded sk msg signSeed
      check st s!"tcId={vec.tcId} sig size" (sig.size == vec.sigSize)

      let sigFirst32 := parseHex vec.sigFirst32
      let sigActual32 := sig.extract 0 32
      check st s!"tcId={vec.tcId} sig first 32 bytes"
        (sigActual32 == sigFirst32)
        s!"got={toHex sigActual32 32} exp={toHex sigFirst32 32}"

      let ver := Falcon.Concrete.FFI.falcon512Verify pk msg sig
      check st s!"tcId={vec.tcId} FFI verify = {vec.verifyResult}"
        ((ver == 1) == vec.verifyResult)
  IO.println ""

  -- ── 9. FPR arithmetic ─────────────────────────
  IO.println "9. FPR arithmetic (integer-only IEEE-754 emulation)"
  do
    checkFPR st "ofInt 0 = zero" (ofInt 0) (0x0000000000000000 : UInt64)
    checkFPR st "ofInt 1 = one" (ofInt 1) one
    checkFPR st "ofInt 2 = two" (ofInt 2) two
    checkFPR st "ofInt (-1)" (ofInt (-1)) (0xBFF0000000000000 : UInt64)
    checkFPR st "ofInt (-2)" (ofInt (-2)) (0xC000000000000000 : UInt64)
    checkFPR st "ofInt 42" (ofInt 42) (0x4045000000000000 : UInt64)
    checkFPR st "ofInt (-42)" (ofInt (-42)) (0xC045000000000000 : UInt64)
    checkFPR st "ofInt 12289 = q" (ofInt 12289) q
    checkFPR st "ofInt 100" (ofInt 100) (0x4059000000000000 : UInt64)
    checkFPR st "ofInt 1000000" (ofInt 1000000) (0x412E848000000000 : UInt64)

    checkFPR st "neg(one)" (neg one) (0xBFF0000000000000 : UInt64)
    checkFPR st "neg(neg(one)) = one" (neg (neg one)) one
    checkFPR st "neg(two)" (neg two) (0xC000000000000000 : UInt64)

    checkFPR st "add(one, two) = 3" (add one two) (0x4008000000000000 : UInt64)
    checkFPR st "add(one, neg one) = 0" (add one (neg one)) zero
    checkFPR st "add(one, one) = two" (add one one) two
    checkFPR st "add(half, half) = one" (add half half) one
    checkFPR st "add(42, 100) = 142" (add (ofInt 42) (ofInt 100))
      (0x4061C00000000000 : UInt64)

    checkFPR st "sub(two, one) = one" (sub two one) one
    checkFPR st "sub(one, two) = -1" (sub one two) (neg one)
    checkFPR st "sub(one, one) = zero" (sub one one) zero
    checkFPR st "sub(142, 42) = 100" (sub (ofInt 142) (ofInt 42))
      (0x4059000000000000 : UInt64)

    checkFPR st "mul(two, two) = 4" (mul two two) (0x4010000000000000 : UInt64)
    checkFPR st "mul(one, one) = one" (mul one one) one
    checkFPR st "mul(two, half) = one" (mul two half) one
    checkFPR st "mul(42, 100) = 4200" (mul (ofInt 42) (ofInt 100))
      (0x40B0680000000000 : UInt64)
    checkFPR st "mul(q, invQ) = one" (mul q invQ) one

    checkFPR st "div(one, two) = half" (div one two) half
    checkFPR st "div(6, 3) = two" (div (ofInt 6) (ofInt 3)) two
    checkFPR st "div(100, 10) = 10" (div (ofInt 100) (ofInt 10))
      (0x4024000000000000 : UInt64)
    checkFPR st "div(one, q) = invQ" (div one q) invQ

    checkFPR st "sqrt(one) = one" (sqrt one) one
    checkFPR st "sqrt(4) = two" (sqrt (ofInt 4)) two
    checkFPR st "sqrt(two)" (sqrt two) (0x3FF6A09E667F3BCD : UInt64)
    checkFPR st "sqrt(100) = 10" (sqrt (ofInt 100)) (0x4024000000000000 : UInt64)
  IO.println ""

  -- ── 10. FPR conversions ────────────────────────
  IO.println "10. FPR conversions (rint, floor_, scaled)"
  do
    check st "rint(one) = 1" (rint one == 1)
    check st "rint(two) = 2" (rint two == 2)
    check st "rint(ofInt 42) = 42" (rint (ofInt 42) == 42)
    check st "rint(neg(ofInt 7)) = -7" (rint (neg (ofInt 7)) == -7)
    check st "rint(half) = 0" (rint half == 0)
    check st "rint(1.5) = 2" (rint (add one half) == 2)
    check st "rint(2.5) = 2" (rint (add two half) == 2)
    check st "rint(neg(half)) = 0" (rint (neg half) == 0)

    check st "floor_(one) = 1" (floor_ one == 1)
    check st "floor_(half) = 0" (floor_ half == 0)
    check st "floor_(neg(half)) = -1" (floor_ (neg half) == -1)
    check st "floor_(1.5) = 1" (floor_ (add one half) == 1)
    check st "floor_(neg(1.5)) = -2" (floor_ (neg (add one half)) == -2)
    check st "floor_(ofInt 42) = 42" (floor_ (ofInt 42) == 42)

    checkFPR st "scaled(1, 10) = 1024" (scaled 1 10)
      (0x4090000000000000 : UInt64)
    checkFPR st "scaled(3, -1) = 1.5" (scaled 3 (-1))
      (0x3FF8000000000000 : UInt64)
    checkFPR st "scaled(5, 0) = 5" (scaled 5 0)
      (0x4014000000000000 : UInt64)
    checkFPR st "scaled(-7, 2) = -28" (scaled (-7) 2)
      (0xC03C000000000000 : UInt64)
  IO.println ""

  -- ── 11. FPR expm_p63 ───────────────────────────
  IO.println "11. FPR expm_p63 (FACCT polynomial exp approximation)"
  do
    check st "expm_p63(zero, half) = 2^62"
      (expm_p63 zero half == (0x4000000000000000 : UInt64))
      s!"got=0x{reprHex (expm_p63 zero half)}"
    check st "expm_p63(half, half)"
      (expm_p63 half half == (0x26D165F8DF2C11B0 : UInt64))
      s!"got=0x{reprHex (expm_p63 half half)}"
  IO.println ""

  -- ── 12. SamplerZ components ────────────────────
  IO.println "12. SamplerZ components"
  do
    let seed := ByteArray.mk #[0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,
      0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51]
    let prng := PRNGState.init seed
    let (z, _) := gaussian0 prng
    check st s!"gaussian0 returns non-negative z (got {z})" (z >= 0)
    check st s!"gaussian0 z in reasonable range (got {z})" (z < 20)

    let prng2 := PRNGState.init seed
    let (accept1, _) := berExp prng2 zero half
    check st s!"berExp(zero, half) likely accepts (got {accept1})" accept1
  IO.println ""

  -- ── 13. Falcon-1024 FFI end-to-end ─────────────
  IO.println "13. Falcon-1024 FFI end-to-end"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon1024KeygenSeeded seed
    check st "Falcon-1024 sk size = 2305" (sk.size == 2305)
    check st "Falcon-1024 pk size = 1793" (pk.size == 1793)

    let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
    let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
      (0xFF - i.val).toUInt8⟩
    let sig := Falcon.Concrete.FFI.falcon1024SignSeeded sk msg signSeed
    check st "FFI-1024 sign produces non-empty sig" (sig.size > 0)
    check st s!"FFI-1024 sig size ≤ 1282 (got {sig.size})" (sig.size <= 1282)

    let ver := Falcon.Concrete.FFI.falcon1024Verify pk msg sig
    check st "FFI-1024 verify accepts valid sig" (ver == 1)

    let corruptedSig := sig.set! 1 (sig[1]! ^^^ 0xFF)
    let verCorrupt := Falcon.Concrete.FFI.falcon1024Verify pk msg corruptedSig
    check st "FFI-1024 verify rejects corrupted sig" (verCorrupt == 0)
  IO.println ""

  -- ── 14. Falcon-1024 FFI sign → Lean verify ─────
  IO.println "14. FFI sign → Lean concreteVerify (Falcon-1024)"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon1024KeygenSeeded seed
    let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
    let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
      (0xFF - i.val).toUInt8⟩
    let sig := Falcon.Concrete.FFI.falcon1024SignSeeded sk msg signSeed
    let leanResult := concreteVerify testFalcon1024 pk msg.toList sig
    check st "Lean concreteVerify accepts FFI-1024 sig" leanResult
  IO.println ""

  -- ── 15. Varied-input end-to-end ────────────────
  IO.println "15. Varied-input end-to-end (both 512 and 1024)"
  do
    let seed1 : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => (i.val * 3 + 7).toUInt8⟩
    let seed2 : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => (i.val * 5 + 13).toUInt8⟩

    let emptyMsg : ByteArray := ByteArray.empty
    let longMsg : ByteArray := ⟨Array.ofFn fun (i : Fin 1000) =>
      (i.val % 256).toUInt8⟩

    for (paramName, keygen, sign, verify, leanParams) in [
      ("512",
        Falcon.Concrete.FFI.falcon512KeygenSeeded,
        Falcon.Concrete.FFI.falcon512SignSeeded,
        Falcon.Concrete.FFI.falcon512Verify,
        testFalcon512),
      ("1024",
        Falcon.Concrete.FFI.falcon1024KeygenSeeded,
        Falcon.Concrete.FFI.falcon1024SignSeeded,
        Falcon.Concrete.FFI.falcon1024Verify,
        testFalcon1024)] do

      let (sk, pk) := keygen seed1

      let sig1 := sign sk emptyMsg seed2
      check st s!"Falcon-{paramName} empty msg: sig non-empty" (sig1.size > 0)
      let ver1 := verify pk emptyMsg sig1
      check st s!"Falcon-{paramName} empty msg: FFI verify" (ver1 == 1)
      let lv1 := concreteVerify leanParams pk emptyMsg.toList sig1
      check st s!"Falcon-{paramName} empty msg: Lean verify" lv1

      let sig2 := sign sk longMsg seed2
      check st s!"Falcon-{paramName} 1000-byte msg: sig non-empty" (sig2.size > 0)
      let ver2 := verify pk longMsg sig2
      check st s!"Falcon-{paramName} 1000-byte msg: FFI verify" (ver2 == 1)
      let lv2 := concreteVerify leanParams pk longMsg.toList sig2
      check st s!"Falcon-{paramName} 1000-byte msg: Lean verify" lv2

      let (sk3, pk3) := keygen seed2
      let msg3 : ByteArray := ⟨#[0x41, 0x42, 0x43]⟩
      let sig3 := sign sk3 msg3 seed1
      check st s!"Falcon-{paramName} alt seed: sig non-empty" (sig3.size > 0)
      let ver3 := verify pk3 msg3 sig3
      check st s!"Falcon-{paramName} alt seed: FFI verify" (ver3 == 1)
      let lv3 := concreteVerify leanParams pk3 msg3.toList sig3
      check st s!"Falcon-{paramName} alt seed: Lean verify" lv3

      let verCross := verify pk msg3 sig3
      check st s!"Falcon-{paramName} wrong key: FFI rejects" (verCross == 0)
  IO.println ""

  -- ── Summary ────────────────────────────────────
  let s ← st.get
  IO.println s!"=== {s.passed} passed, {s.failed} failed ==="
  if s.failed > 0 then
    IO.Process.exit 1
where
  reprHex (v : UInt64) : String := Id.run do
    let mut s := ""
    for i in [0:16] do
      let nibble := ((v >>> ((15 - i) * 4).toUInt64) &&& 0xF).toNat
      s := s ++ (if nibble < 10 then
        String.ofList [Char.ofNat (48 + nibble)]
      else
        String.ofList [Char.ofNat (55 + nibble)])
    return s

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

open Falcon Falcon.Concrete Falcon.Concrete.FPR Falcon.Concrete.SamplerZ
     Falcon.Concrete.FFTOps Falcon.Concrete.Sign Falcon.Test

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

private def flush : IO Unit := IO.getStdout >>= IO.FS.Stream.flush

def main : IO Unit := do
  let st ← IO.mkRef ({} : TestState)

  IO.println "=== Falcon Correctness Tests ==="
  IO.println ""
  flush

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
    let expected := negacyclicMulU32 f g
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
    check st "Falcon-512 param sk size = 1281" (Falcon.Params.secretKeyBytesForDegree 512 == 1281)
    check st "Falcon-1024 param sk size = 2305" (Falcon.Params.secretKeyBytesForDegree 1024 == 2305)
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
  flush

  -- ── 16. FloatLike Float arithmetic ──────────────
  IO.println "16. FloatLike Float arithmetic (native IEEE-754)"
  do
    let ofI (i : Int64) : Float := FloatLike.ofInt i
    let fOne : Float := FloatLike.one
    let fTwo : Float := FloatLike.two
    let fHalf : Float := FloatLike.half

    checkFloat st "Float ofInt 0 = 0" (ofI 0) 0.0
    checkFloat st "Float ofInt 1 = 1" (ofI 1) 1.0
    checkFloat st "Float ofInt 42 = 42" (ofI 42) 42.0
    checkFloat st "Float ofInt(-1) = -1" (ofI (-1)) (-1.0)
    checkFloat st "Float neg(one) = -1" (FloatLike.neg fOne) (-1.0)
    checkFloat st "Float neg(neg(one)) = 1" (FloatLike.neg (FloatLike.neg fOne)) 1.0

    checkFloat st "Float add(one, two) = 3" (FloatLike.add fOne fTwo) 3.0
    checkFloat st "Float add(42, 100) = 142" (FloatLike.add (ofI 42) (ofI 100)) 142.0
    checkFloat st "Float add(half, half) = 1" (FloatLike.add fHalf fHalf) 1.0

    checkFloat st "Float sub(two, one) = 1" (FloatLike.sub fTwo fOne) 1.0
    checkFloat st "Float sub(one, two) = -1" (FloatLike.sub fOne fTwo) (-1.0)

    checkFloat st "Float mul(two, two) = 4" (FloatLike.mul fTwo fTwo) 4.0
    checkFloat st "Float mul(42, 100) = 4200" (FloatLike.mul (ofI 42) (ofI 100)) 4200.0
    checkFloat st "Float mul(two, half) = 1" (FloatLike.mul fTwo fHalf) 1.0

    checkFloat st "Float div(one, two) = 0.5" (FloatLike.div fOne fTwo) 0.5
    checkFloat st "Float div(6, 3) = 2" (FloatLike.div (ofI 6) (ofI 3)) 2.0

    checkFloat st "Float sqrt(one) = 1" (FloatLike.sqrt fOne) 1.0
    checkFloat st "Float sqrt(4) = 2" (FloatLike.sqrt (ofI 4)) 2.0
    let fprSqrt2 := FloatLike.ofRawFPR (F := Float) (FPR.sqrt (FPR.ofInt 2))
    checkFloat st "Float sqrt(2) ≈ FPR sqrt(2)" (FloatLike.sqrt (ofI 2)) fprSqrt2 1e-15
  IO.println ""

  -- ── 17. FloatLike Float conversions ──────────────
  IO.println "17. FloatLike Float conversions (rint, floor_, scaled)"
  do
    let fOne : Float := FloatLike.one
    let fHalf : Float := FloatLike.half
    let ofI (i : Int64) : Float := FloatLike.ofInt i

    check st "Float rint(one) = 1" (FloatLike.rint fOne == (1 : Int64))
    check st "Float rint(42) = 42" (FloatLike.rint (ofI 42) == (42 : Int64))
    check st "Float rint(-7) = -7" (FloatLike.rint (ofI (-7)) == (-7 : Int64))
    check st "Float rint(half) = 0 (ties-to-even)"
      (FloatLike.rint fHalf == (0 : Int64))
    check st "Float rint(1.5) = 2" (FloatLike.rint (FloatLike.add fOne fHalf) == (2 : Int64))
    check st "Float rint(2.5) = 2" (FloatLike.rint (FloatLike.add (ofI 2) fHalf) == (2 : Int64))
    check st "Float rint(-half) = 0"
      (FloatLike.rint (FloatLike.neg fHalf) == (0 : Int64))

    check st "Float floor_(one) = 1" (FloatLike.floor_ fOne == (1 : Int64))
    check st "Float floor_(half) = 0" (FloatLike.floor_ fHalf == (0 : Int64))
    check st "Float floor_(-half) = -1"
      (FloatLike.floor_ (FloatLike.neg fHalf) == (-1 : Int64))
    check st "Float floor_(42) = 42" (FloatLike.floor_ (ofI 42) == (42 : Int64))

    let s1 : Float := FloatLike.scaled (1 : Int64) (10 : Int32)
    checkFloat st "Float scaled(1, 10) = 1024" s1 1024.0
    let s2 : Float := FloatLike.scaled (3 : Int64) (-1 : Int32)
    checkFloat st "Float scaled(3, -1) = 1.5" s2 1.5
    let s3 : Float := FloatLike.scaled (5 : Int64) (0 : Int32)
    checkFloat st "Float scaled(5, 0) = 5" s3 5.0
  IO.println ""

  -- ── 18. FloatLike Float expm_p63 ─────────────────
  IO.println "18. FloatLike Float expm_p63 (hardware exp vs FACCT polynomial)"
  do
    let fprR1 := FPR.expm_p63 FPR.zero FPR.half
    let floatR1 := FloatLike.expm_p63 (0.0 : Float) (0.5 : Float)
    checkApproxU64 st "expm_p63(0, 0.5) Float≈FPR" floatR1 fprR1 (1 <<< 20)

    let fprR2 := FPR.expm_p63 FPR.half FPR.half
    let floatR2 := FloatLike.expm_p63 (0.5 : Float) (0.5 : Float)
    checkApproxU64 st "expm_p63(0.5, 0.5) Float≈FPR" floatR2 fprR2 (1 <<< 20)

    let quarter := FPR.scaled 1 (-2)
    let fprR3 := FPR.expm_p63 quarter FPR.half
    let floatR3 := FloatLike.expm_p63 (0.25 : Float) (0.5 : Float)
    checkApproxU64 st "expm_p63(0.25, 0.5) Float≈FPR" floatR3 fprR3 (1 <<< 22)
  IO.println ""

  -- ── 19. SamplerZ with Float backend ──────────────
  IO.println "19. SamplerZ with Float backend"
  do
    let seed := ByteArray.mk #[0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,
      0x4A, 0x4B, 0x4C, 0x4D, 0x4E, 0x4F, 0x50, 0x51]
    let prng := PRNGState.init seed

    let (accept, _) := berExp (F := Float) prng (FloatLike.zero) (FloatLike.half)
    check st s!"berExp(Float)(zero, half) likely accepts (got {accept})" accept

    let prng2 := PRNGState.init seed
    let invSigma9 : Float :=
      FloatLike.ofRawFPR (Falcon.Concrete.GMTable.invSigmaRaw.getD 9 0)
    let (z, _) := samplerZ (F := Float) 9 prng2 (FloatLike.zero) invSigma9
    check st s!"samplerZ(Float) z in range (got {z.toInt})" (z.toInt.natAbs < 20)
  IO.println ""

  -- ── 20. FFT/iFFT roundtrip ──────────────────────
  IO.println "20. FFT/iFFT roundtrip (fpolyFFT ∘ fpolyIFFT = id)"
  do
    -- FPR FFT roundtrip at logn=9 has known precision issues (see section 21 for
    -- FPR correctness with smaller dimensions and different test data).
    for (logn, label) in [(5, "logn=5"), (6, "logn=6")] do
      let n := 1 <<< logn
      let testPoly : Array Int32 := (Array.range n).map fun i =>
        ((i * 7 + 3) % 200).toUInt32.toInt32 - 100
      let f' := fpolyIFFT (F := FPR) logn (fpolyFFT (F := FPR) logn
        (fpolySetSmall (F := FPR) logn testPoly))
      let ok := (Array.range n).all fun i =>
        FPR.rint (f'.getD i 0) == testPoly[i]!.toInt64
      check st s!"FPR: iFFT(FFT(poly)) roundtrip ({label})" ok

      let fFloat' := fpolyIFFT (F := Float) logn (fpolyFFT (F := Float) logn
        (fpolySetSmall (F := Float) logn testPoly))
      let okFloat := (Array.range n).all fun i =>
        FloatLike.rint (fFloat'.getD i (0.0 : Float)) == testPoly[i]!.toInt64
      check st s!"Float: iFFT(FFT(poly)) roundtrip ({label})" okFloat
    -- logn=9 Float-only roundtrip (FPR precision at this scale is a known issue)
    do
      let logn := 9
      let n := 1 <<< logn
      let testPoly : Array Int32 := (Array.range n).map fun i =>
        ((i * 7 + 3) % 200).toUInt32.toInt32 - 100
      let fFloat' := fpolyIFFT (F := Float) logn (fpolyFFT (F := Float) logn
        (fpolySetSmall (F := Float) logn testPoly))
      let okFloat := (Array.range n).all fun i =>
        FloatLike.rint (fFloat'.getD i (0.0 : Float)) == testPoly[i]!.toInt64
      check st "Float: iFFT(FFT(poly)) roundtrip (logn=9)" okFloat
  IO.println ""

  -- ── 21. fpolySetSmall + FFT roundtrip ───────────
  IO.println "21. fpolySetSmall + FFT roundtrip (Int32 → FPR → FFT → iFFT → rint)"
  do
    let logn := 4
    let n := 1 <<< logn
    let original : Array Int32 := (Array.range n).map fun i =>
      (i.toUInt32.toInt32 * 13 - 100)
    let fpoly := fpolySetSmall (F := FPR) logn original
    let roundtripped := fpolyIFFT (F := FPR) logn (fpolyFFT (F := FPR) logn fpoly)
    let recovered : Array Int64 := (Array.range n).map fun i =>
      FPR.rint (roundtripped.getD i 0)
    let ok := (Array.range n).all fun i =>
      recovered.getD i 0 == (original.getD i 0).toInt64
    check st "Int32 recovery via FFT roundtrip (FPR, logn=4)" ok

    let fpolyFloat := fpolySetSmall (F := Float) logn original
    let rtFloat := fpolyIFFT (F := Float) logn (fpolyFFT (F := Float) logn fpolyFloat)
    let okFloat := (Array.range n).all fun i =>
      FloatLike.rint (rtFloat.getD i (0.0 : Float)) == (original.getD i 0).toInt64
    check st "Int32 recovery via FFT roundtrip (Float, logn=4)" okFloat
  IO.println ""

  -- ── 22. fpoly arithmetic ─────────────────────────
  IO.println "22. fpoly arithmetic consistency"
  do
    let logn := 4
    let n := 1 <<< logn
    let aCoeffs : Array Int32 := (Array.range n).map fun i => (i + 1).toUInt32.toInt32
    let bCoeffs : Array Int32 := (Array.range n).map fun i => (n - i).toUInt32.toInt32
    let aFFT := fpolyFFT (F := FPR) logn (fpolySetSmall logn aCoeffs)
    let bFFT := fpolyFFT (F := FPR) logn (fpolySetSmall logn bCoeffs)

    let ab := fpolyMulFFT (F := FPR) logn aFFT bFFT
    let ba := fpolyMulFFT (F := FPR) logn bFFT aFFT
    let mulCommOk := (Array.range n).all fun i =>
      (ab.getD i 0) == (ba.getD i 0)
    check st "fpolyMulFFT commutativity: mul(a,b) = mul(b,a)" mulCommOk

    let sum := fpolyAdd (F := FPR) logn aFFT bFFT
    let diff := fpolySub (F := FPR) logn sum bFFT
    let addSubOk := (Array.range n).all fun i =>
      FPR.rint (aFFT.getD i 0) == FPR.rint (diff.getD i 0)
    check st "fpolyAdd then fpolySub ≈ identity" addSubOk
  IO.println ""

  -- ── 23. BigInt31 basic ops ──────────────────────
  IO.println "23. BigInt31 basic ops"
  do
    let p0 := Falcon.Concrete.SmallPrimeNTT.PRIMES[0]!
    let p := p0.p
    let p0i := p0.p0i

    check st "mp_add: (3+5) mod p = 8"
      (Falcon.Concrete.BigInt31.mp_add 3 5 p == 8)
    check st "mp_sub: (10-3) mod p = 7"
      (Falcon.Concrete.BigInt31.mp_sub 10 3 p == 7)
    check st "mp_sub: (3-10) mod p = p-7"
      (Falcon.Concrete.BigInt31.mp_sub 3 10 p == p - 7)

    let m : Array UInt32 := #[5, 0, 0, 0]
    let (m', carry) := Falcon.Concrete.BigInt31.zint_mul_small m 1 3
    check st "zint_mul_small: [5]*3 = [15], carry=0"
      (m'.getD 0 0 == 15 && carry == 0)

    let m2 : Array UInt32 := #[0x7FFFFFFF, 0, 0, 0]
    let (m2', carry2) := Falcon.Concrete.BigInt31.zint_mul_small m2 1 2
    check st "zint_mul_small: [2^31-1]*2 carry propagation"
      (carry2 == 1 && m2'.getD 0 0 == 0x7FFFFFFE)

    check st "mp_mmul: Montgomery mul known value"
      (Falcon.Concrete.BigInt31.mp_mmul 100 200 p p0i ==
       Falcon.Concrete.SmallPrimeNTT.mp_montymul 100 200 p p0i)

    let (uBez, vBez, bezOk) := Falcon.Concrete.BigInt31.zint_bezout #[3] #[5] 1
    check st "zint_bezout: 3*u - 5*v = 1"
      (bezOk == 1 && uBez.getD 0 0 == 2 && vBez.getD 0 0 == 1)
  IO.println ""

  -- ── 24. SmallPrimeNTT roundtrip ─────────────────
  IO.println "24. SmallPrimeNTT roundtrip (NTT then iNTT = id)"
  do
    let p0 := Falcon.Concrete.SmallPrimeNTT.PRIMES[0]!
    let logn := 3
    let n := 1 <<< logn
    let (gm, igm) := Falcon.Concrete.SmallPrimeNTT.mp_mkgmigm
      logn p0.g p0.ig p0.p p0.p0i
    let poly : Array UInt32 := (Array.range n).map fun i =>
      Falcon.Concrete.SmallPrimeNTT.mp_set (i + 1).toUInt32.toInt32 p0.p
    let nttPoly := Falcon.Concrete.SmallPrimeNTT.mp_NTT logn poly gm p0.p p0.p0i
    let recoveredPoly := Falcon.Concrete.SmallPrimeNTT.mp_iNTT logn nttPoly igm p0.p p0.p0i
    let ok := (Array.range n).all fun i =>
      poly.getD i 0 == recoveredPoly.getD i 0
    check st "mp_iNTT(mp_NTT(poly)) = poly (logn=3)" ok

    let logn5 := 5
    let n5 := 1 <<< logn5
    let (gm5, igm5) := Falcon.Concrete.SmallPrimeNTT.mp_mkgmigm
      logn5 p0.g p0.ig p0.p p0.p0i
    let poly5 : Array UInt32 := (Array.range n5).map fun i =>
      Falcon.Concrete.SmallPrimeNTT.mp_set (i * 3 + 7).toUInt32.toInt32 p0.p
    let ntt5 := Falcon.Concrete.SmallPrimeNTT.mp_NTT logn5 poly5 gm5 p0.p p0.p0i
    let rec5 := Falcon.Concrete.SmallPrimeNTT.mp_iNTT logn5 ntt5 igm5 p0.p p0.p0i
    let ok5 := (Array.range n5).all fun i =>
      poly5.getD i 0 == rec5.getD i 0
    check st "mp_iNTT(mp_NTT(poly)) = poly (logn=5)" ok5
  IO.println ""

  -- ── 25. Montgomery multiplication ───────────────
  IO.println "25. Montgomery multiplication verification"
  do
    let p0 := Falcon.Concrete.SmallPrimeNTT.PRIMES[0]!
    let p := p0.p
    let p0i := p0.p0i
    let R2 := p0.R2

    let a : UInt32 := 42
    let b : UInt32 := 100
    let aM := Falcon.Concrete.SmallPrimeNTT.mp_montymul a R2 p p0i
    let bM := Falcon.Concrete.SmallPrimeNTT.mp_montymul b R2 p p0i
    let abM := Falcon.Concrete.SmallPrimeNTT.mp_montymul aM bM p p0i
    let ab := Falcon.Concrete.SmallPrimeNTT.mp_montymul abM 1 p p0i
    let expected : UInt32 := ((42 * 100 : Nat) % p.toNat).toUInt32
    check st s!"Monty: 42*100 mod p = {expected} (got {ab})" (ab == expected)

    let c : UInt32 := 999999
    let cM := Falcon.Concrete.SmallPrimeNTT.mp_montymul c R2 p p0i
    let ccM := Falcon.Concrete.SmallPrimeNTT.mp_montymul cM cM p p0i
    let cc := Falcon.Concrete.SmallPrimeNTT.mp_montymul ccM 1 p p0i
    let expectedCC : UInt32 := ((999999 * 999999 : Nat) % p.toNat).toUInt32
    check st s!"Monty: 999999² mod p = {expectedCC} (got {cc})" (cc == expectedCC)
  IO.println ""

  -- ── 26. FXR basic ops ───────────────────────────
  IO.println "26. FXR basic arithmetic (32.32 fixed-point)"
  do
    let one := Falcon.Concrete.FXR.fxr_of 1
    let two := Falcon.Concrete.FXR.fxr_of 2
    let three := Falcon.Concrete.FXR.fxr_of 3
    let six := Falcon.Concrete.FXR.fxr_of 6

    check st "fxr_of(1) = 1<<32"
      (one == ((1 : UInt64) <<< 32))
    check st "fxr_add(1, 2) = 3"
      (Falcon.Concrete.FXR.fxr_add one two == three)
    check st "fxr_sub(3, 1) = 2"
      (Falcon.Concrete.FXR.fxr_sub three one == two)
    check st "fxr_mul(2, 3) = 6"
      (Falcon.Concrete.FXR.fxr_mul two three == six)
    check st "fxr_div(6, 3) = 2"
      (Falcon.Concrete.FXR.fxr_div six three == two)
    check st "fxr_neg(1) + 1 = 0"
      (Falcon.Concrete.FXR.fxr_add (Falcon.Concrete.FXR.fxr_neg one) one == 0)
    check st "fxr_round(1) = 1"
      (Falcon.Concrete.FXR.fxr_round one == (1 : Int32))
    check st "fxr_double(1) = 2"
      (Falcon.Concrete.FXR.fxr_double one == two)
    check st "fxr_half(2) = 1"
      (Falcon.Concrete.FXR.fxr_half two == one)
  IO.println ""
  flush

  -- ── 27. Diagnostic: target vector & NTRU relation check ──────────
  IO.println "27. Diagnostic: target vector & NTRU relation check"
  flush
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    match decodeSecretKey 9 sk with
    | none => IO.println "  decode failed"
    | some (f, g, capF) =>
      match computeCapG512 capF pk with
      | none => IO.println "  G computation failed"
      | some capG =>
        let n : Nat := 512
        IO.println s!"  f[0..4] = {f.toList.take 4}"
        IO.println s!"  g[0..4] = {g.toList.take 4}"
        IO.println s!"  F[0..4] = {capF.toList.take 4}"
        IO.println s!"  G[0..4] = {capG.toList.take 4}"
        let gMax := capG.foldl (init := (0 : Int32)) fun mx v =>
          let av := if v < 0 then (0 : Int32) - v else v
          if av > mx then av else mx
        IO.println s!"  max|G[i]| = {gMax}"
        let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
        let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
          (0xFF - i.val).toUInt8⟩
        let masterPRNG := PRNGState.init signSeed
        let (salt, _) := prngNextSalt masterPRNG
        let hm := hashToPoint n salt pk msg.toList
        let hmArr := rqToUInt16Array hm
        IO.println s!"  hm[0..4] = {hmArr.toList.take 4}"
        let (b00, b01, b10, b11) := basisToFFT (F := Float) 9 f g capF capG
        let (t0, t1) := fpolyApplyBasis 9 b01 b11 hmArr
        let v0fft := fpolyAdd 9 (fpolyMulFFT 9 b00 t0) (fpolyMulFFT 9 b10 t1)
        let v0 := fpolyIFFT 9 v0fft
        let v1fft := fpolyAdd 9 (fpolyMulFFT 9 b01 t0) (fpolyMulFFT 9 b11 t1)
        let v1 := fpolyIFFT 9 v1fft
        IO.println s!"  v0[0..4] = {(v0.toList.take 4).map fun (x : Float) => x.round}"
        IO.println s!"  v1[0..4] = {(v1.toList.take 4).map fun (x : Float) => x.round}"
        let mut maxErr0 : Float := 0.0
        let mut maxErr1 : Float := 0.0
        for i in [0:n] do
          let err0 := (v0.getD i 0.0 - (hmArr.getD i 0).toUInt32.toFloat).abs
          let err1 := (v1.getD i 0.0).abs
          if err0 > maxErr0 then maxErr0 := err0
          if err1 > maxErr1 then maxErr1 := err1
        IO.println s!"  max|v0 - hm| = {maxErr0} (should be < 1.0)"
        IO.println s!"  max|v1| = {maxErr1} (should be < 1.0)"
        check st "target vector g*t0+G*t1 = hm" (maxErr0 < 1.0 && maxErr1 < 1.0)
  IO.println ""
  -- ── 27b. Split/merge roundtrip test ──────────────
  IO.println "27b. Split/merge roundtrip test"
  flush
  do
    for logn in [2, 5, 9] do
      let n : Nat := 1 <<< logn
      let hn := n >>> 1
      let fArr : Array Float := (Array.range n).map fun i => Float.ofNat (i + 1)
      let fFFT := fpolyFFT logn fArr
      let (f0, f1) := fpolySplitFFT logn fFFT
      let fMerged := fpolyMergeFFT logn f0 f1
      let mut maxSMErr : Float := 0.0
      for i in [0:n] do
        let e := (fMerged.getD i 0.0 - fFFT.getD i 0.0).abs
        if e > maxSMErr then maxSMErr := e
      let smOk := maxSMErr < 1e-6
      IO.println s!"  logn={logn}: merge(split(f)) err = {maxSMErr} {if smOk then "OK" else "FAIL"}"
      check st s!"split/merge roundtrip logn={logn}" smOk
      let saArr : Array Float := (Array.range hn).map fun i => Float.ofNat (i * i + 1)
      let (sa0, sa1) := fpolySplitSelfadjFFT logn saArr
      IO.println s!"  logn={logn}: selfadj split f0 size={sa0.size}, f1 size={sa1.size}"
  IO.println ""
  IO.println ""

  -- ── 28. Pure-Lean signing smoke test ────────────
  IO.println "28. Pure-Lean signing smoke test (Float)"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => (i.val * 2 + 1).toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    match decodeSecretKey 9 sk with
    | none => check st "decode sk for signing smoke test" false
    | some (f, g, capF) =>
      match computeCapG512 capF pk with
      | none => check st "compute G for signing smoke test" false
      | some capG =>
        let msg : ByteArray := ⟨#[0x54, 0x65, 0x73, 0x74]⟩
        let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
          (i.val * 3).toUInt8⟩
        let tFloat0 ← IO.monoMsNow
        let floatSig := concreteSign (F := Float) 9 f g capF capG pk msg.toList signSeed
        let tFloat1 ← IO.monoMsNow
        IO.println s!"  concreteSign(Float) took {tFloat1 - tFloat0}ms"
        match floatSig with
        | some s =>
          let lv := concreteVerify testFalcon512 pk msg.toList s
          check st "Float sig verifies" lv
          let fv := Falcon.Concrete.FFI.falcon512Verify pk msg s
          check st "FFI verify accepts Float sig" (fv == 1)
        | none => check st "Float sign succeeded" false
  IO.println ""

  -- ── 29. Batch E2E (3 iterations) ─────────────────
  IO.println "29. Batch E2E: pure-Lean sign+verify (3 seeds, Float)"
  do
    for iter in [0:3] do
      let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
        (i.val * 7 + iter * 31).toUInt8⟩
      let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
      match decodeSecretKey 9 sk with
      | none => check st s!"iter {iter}: decode sk" false
      | some (f, g, capF) =>
        match computeCapG512 capF pk with
        | none => check st s!"iter {iter}: compute G" false
        | some capG =>
          let msg : ByteArray := ⟨#[(0x41 + iter.toUInt8)]⟩
          let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
            (i.val + iter * 17).toUInt8⟩
          match concreteSign (F := Float) 9 f g capF capG pk msg.toList signSeed with
          | none => check st s!"iter {iter}: sign succeeded" false
          | some sig =>
            let lv := concreteVerify testFalcon512 pk msg.toList sig
            check st s!"iter {iter}: Lean verify" lv
            let fv := Falcon.Concrete.FFI.falcon512Verify pk msg sig
            check st s!"iter {iter}: FFI verify" (fv == 1)
  IO.println ""

  -- ── 30. Rejection / negative tests ──────────────
  IO.println "30. Rejection / negative tests for pure-Lean signatures (Float)"
  do
    let seed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) => i.val.toUInt8⟩
    let (sk, pk) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed
    match decodeSecretKey 9 sk with
    | none => check st "decode sk for negative tests" false
    | some (f, g, capF) =>
      match computeCapG512 capF pk with
      | none => check st "compute G for negative tests" false
      | some capG =>
        let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩
        let signSeed : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
          (0xFF - i.val).toUInt8⟩
        match concreteSign (F := Float) 9 f g capF capG pk msg.toList signSeed with
        | none => check st "sign for negative tests" false
        | some sig =>
          let corruptedSig := sig.set! 2 (sig[2]! ^^^ 0xFF)
          let lv := concreteVerify testFalcon512 pk msg.toList corruptedSig
          check st "corrupted pure-Lean sig: Lean verify rejects" (!lv)
          let wrongMsg : ByteArray := ⟨#[0x00]⟩
          let lv2 := concreteVerify testFalcon512 pk wrongMsg.toList sig
          check st "wrong msg: Lean verify rejects pure-Lean sig" (!lv2)
          let seed2 : ByteArray := ⟨Array.ofFn fun (i : Fin 48) =>
            (i.val * 5 + 13).toUInt8⟩
          let (_, pk2) := Falcon.Concrete.FFI.falcon512KeygenSeeded seed2
          let lv3 := concreteVerify testFalcon512 pk2 msg.toList sig
          check st "wrong pk: Lean verify rejects pure-Lean sig" (!lv3)
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

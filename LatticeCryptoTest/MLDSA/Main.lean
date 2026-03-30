/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCryptoTest.MLDSA.Helpers
import LatticeCryptoTest.MLDSA.ACVPVectors

/-!
# ML-DSA-65 Test Runner

Tests the pure-Lean ML-DSA implementation against the verified mldsa-native (v1.0.0-beta) FFI
and NIST known-answer vectors.

## How to run

```bash
git submodule update --init --recursive
lake exe cache get
lake build mldsa_test
.lake/build/bin/mldsa_test
```
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option linter.style.emptyLine false

open MLDSA MLDSA.Concrete MLDSA.Test

/-- Entry point for the ML-DSA regression and interoperability test runner. -/
def main : IO Unit := do
  let st ← IO.mkRef ({} : TestState)

  IO.println "=== ML-DSA-65 Correctness Tests ==="
  IO.println ""

  -- ── 1. NTT roundtrip ──────────────────────────────
  IO.println "1. NTT roundtrip (invNTT ∘ NTT = id)"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i : Coeff)
    let f' := MLDSA.Concrete.invNTT (MLDSA.Concrete.ntt f)
    check st "invNTT(NTT(0,1,…,255)) = (0,1,…,255)" (f == f')

    let g : Rq := Vector.ofFn fun _ => (42 : Coeff)
    let g' := MLDSA.Concrete.invNTT (MLDSA.Concrete.ntt g)
    check st "NTT roundtrip on constant poly" (g == g')

    let h : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 137 + 42 : Coeff)
    let h' := MLDSA.Concrete.invNTT (MLDSA.Concrete.ntt h)
    check st "NTT roundtrip on pseudorandom poly" (h == h')

    let allMax : Rq := Vector.ofFn fun _ => ((modulus - 1 : Nat) : Coeff)
    let allMax' := MLDSA.Concrete.invNTT (MLDSA.Concrete.ntt allMax)
    check st "NTT roundtrip on all-(q-1) poly" (allMax == allMax')
  IO.println ""

  -- ── 2. NTT multiplication ─────────────────────────
  IO.println "2. NTT multiplication"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => if i < 3 then (1 : Coeff) else 0
    let g : Rq := Vector.ofFn fun ⟨i, _⟩ =>
      if i == 0 then (1 : Coeff) else if i == 1 then 2 else 0
    let expected := negacyclicMul f g
    let nttResult := MLDSA.Concrete.invNTT
      (MLDSA.Concrete.multiplyNTTs (MLDSA.Concrete.ntt f) (MLDSA.Concrete.ntt g))
    check st "NTT mul: (1+X+X²)*(1+2X)" (nttResult == expected)

    let one : Rq := Vector.ofFn fun ⟨i, _⟩ => if i == 0 then (1 : Coeff) else 0
    let fHat := MLDSA.Concrete.ntt f
    let oneHat := MLDSA.Concrete.ntt one
    let mulOneResult := MLDSA.Concrete.invNTT
      (MLDSA.Concrete.multiplyNTTs fHat oneHat)
    check st "NTT mul: f * 1 = f" (mulOneResult == f)
  IO.println ""

  -- ── 3. Power2Round roundtrip ───────────────────────
  IO.println "3. Power2Round roundtrip"
  do
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 37 + 13 : Coeff)
    let (hi, lo) := MLDSA.Concrete.power2Round f
    let reconstructed := MLDSA.Concrete.power2RoundShift hi + lo
    check st "power2RoundShift(high) + low = original" (reconstructed == f)

    let allMax : Rq := Vector.ofFn fun _ => ((modulus - 1 : Nat) : Coeff)
    let (hiMax, loMax) := MLDSA.Concrete.power2Round allMax
    let reconMax := MLDSA.Concrete.power2RoundShift hiMax + loMax
    check st "Power2Round roundtrip on all-(q-1)" (reconMax == allMax)
  IO.println ""

  -- ── 4. HighBits/LowBits decomposition ─────────────
  IO.println "4. HighBits/LowBits decomposition"
  do
    let p := mldsa65
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 1337 + 7 : Coeff)
    let hi := MLDSA.Concrete.highBits p f
    let lo := MLDSA.Concrete.lowBits p f
    let reconstructed := MLDSA.Concrete.highBitsShift p hi + lo
    check st "highBitsShift(highBits(r)) + lowBits(r) = r" (reconstructed == f)
  IO.println ""

  -- ── 5. LowBits bound ──────────────────────────────
  IO.println "5. LowBits bound"
  do
    let p := mldsa65
    let f : Rq := Vector.ofFn fun ⟨i, _⟩ => (i * 2017 : Coeff)
    let lo := MLDSA.Concrete.lowBits p f
    let bounded := polyNorm lo ≤ p.gamma2
    check st "‖lowBits(r)‖∞ ≤ γ₂" (decide bounded)
  IO.println ""

  -- ── 6. SampleInBall properties ─────────────────────
  IO.println "6. SampleInBall properties"
  do
    let p := mldsa65
    let cTilde : CommitHashBytes p := Vector.ofFn fun ⟨i, _⟩ => (i * 3).toUInt8
    let c := MLDSA.Concrete.sampleInBall p cTilde
    let weight := c.toArray.foldl (fun acc x => if x == (0 : Coeff) then acc else acc + 1) 0
    check st s!"sampleInBall weight = τ ({p.tau})" (weight == p.tau)
    let allPM1 := c.toArray.all fun x =>
      x == (0 : Coeff) || x == (1 : Coeff) || x == ((modulus - 1 : Nat) : Coeff)
    check st "sampleInBall coefficients ∈ {-1, 0, 1}" allPM1
  IO.println ""

  -- ── 7. Encoding roundtrips ─────────────────────────
  IO.println "7. Encoding roundtrips"
  do
    let p := mldsa65
    let enc := mldsa65Encoding
    let rho : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let t1 : Vector Power2High p.k := Vector.ofFn fun ⟨_j, _⟩ =>
      (Vector.ofFn fun ⟨i, _⟩ =>
        ((i % 1024 : Nat) : Coeff) : Rq)
    let pk := enc.pkEncode rho t1
    let (rho', t1') := enc.pkDecode pk
    check st "pkDecode(pkEncode(ρ, t₁)) = (ρ, t₁)"
      (rho == rho' && t1 == t1')
    let K : Bytes 32 :=
      Vector.ofFn fun ⟨i, _⟩ => (0xFF - i).toUInt8
    let tr : Bytes 64 :=
      Vector.ofFn fun ⟨i, _⟩ => (i * 2).toUInt8
    let eta := p.eta
    let mkEtaPoly (j : Nat) : Rq :=
      Vector.ofFn fun ⟨i, _⟩ =>
        let raw := (i * (j + 1)) % (2 * eta + 1)
        ((raw : ℤ) - (eta : ℤ) : Coeff)
    let s1 : RqVec p.l :=
      Vector.ofFn fun ⟨j, _⟩ => mkEtaPoly j
    let s2 : RqVec p.k :=
      Vector.ofFn fun ⟨j, _⟩ => mkEtaPoly (j + p.l)
    let d2 := (1 <<< MLDSA.droppedBits : Nat) / 2
    let t0 : RqVec p.k := Vector.ofFn fun ⟨j, _⟩ =>
      (Vector.ofFn fun ⟨i, _⟩ =>
        let raw := (i * (j + 3)) % (2 * d2)
        ((raw : ℤ) - ((d2 - 1 : Nat) : ℤ) : Coeff) : Rq)
    let sk := enc.skEncode rho K tr s1 s2 t0
    let (rho'', K', tr', s1', s2', t0') := enc.skDecode sk
    check st "skDecode(skEncode(…)) roundtrip"
      (rho == rho'' && K == K' && tr == tr'
        && s1 == s1' && s2 == s2' && t0 == t0')
  IO.println ""

  -- ── 8. ExpandS bounds ──────────────────────────────
  IO.println "8. ExpandS bounds"
  do
    let p := mldsa65
    let rhoPrime : Bytes 64 := Vector.ofFn fun ⟨i, _⟩ => (i * 5 + 17).toUInt8
    let (s1, s2) := MLDSA.Concrete.expandS rhoPrime p
    let s1Bounded := s1.toArray.all fun poly =>
      poly.toArray.all fun c => c.val ≤ p.eta || c.val ≥ modulus - p.eta
    let s2Bounded := s2.toArray.all fun poly =>
      poly.toArray.all fun c => c.val ≤ p.eta || c.val ≥ modulus - p.eta
    check st s!"expandS s₁ coefficients bounded by η={p.eta}" s1Bounded
    check st s!"expandS s₂ coefficients bounded by η={p.eta}" s2Bounded
  IO.println ""

  -- ── 9. Full keygen: Lean spec vs mldsa-native ─────
  IO.println "9. Full ML-DSA-65 keygen: Lean spec vs mldsa-native"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let seedBA := vectorToByteArray seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
    check st "mldsa-native keygen sizes" (pkRef.size == 1952 && skRef.size == 4032)

    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
    let pkB := serializePK65 pk
    let skB := serializeSK65 sk

    check st "Lean pk size = 1952" (pkB.size == 1952)
    check st "Lean sk size = 4032" (skB.size == 4032)
    check st "pk: Lean spec = mldsa-native" (pkB == pkRef)
      s!"Lean={toHex pkB} ref={toHex pkRef}"
    check st "sk: Lean spec = mldsa-native" (skB == skRef)
      s!"Lean={toHex skB} ref={toHex skRef}"
  IO.println ""

  -- ── 10. Full sign + verify: Lean spec vs mldsa-native ─────
  IO.println "10. Full ML-DSA-65 sign + verify: Lean spec vs mldsa-native"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => i.toUInt8
    let seedBA := vectorToByteArray seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed

    let msg : ByteArray := ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩  -- "Hello"
    let rndZero : ByteArray := ⟨Array.replicate 32 0⟩

    let sigRef := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msg rndZero
    check st "mldsa-native sign produces 3309-byte sig" (sigRef.size == 3309)

    let verRef := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg sigRef
    check st "mldsa-native verify accepts valid sig" (verRef == 1)

    let mu := mldsa65Primitives.hashMessage sk.tr msg.toList
    let rnd : Bytes 32 := Vector.ofFn fun _ => 0
    let rhoDP := mldsa65Primitives.hashPrivateSeed sk.key rnd mu
    let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
      sk (mldsa65Primitives.expandA pk.rho) mu rhoDP 256
    match sigLean with
    | none => check st "Lean signing should succeed" false
    | some sig =>
      let sigB := serializeSig65 sig
      check st "Lean sig size = 3309" (sigB.size == 3309)
      check st "sig: Lean spec = mldsa-native" (sigB == sigRef)
        s!"Lean={toHex sigB} ref={toHex sigRef}"
      let leanVerify := fipsVerify mldsa65 mldsa65Primitives
        concreteNTTRingOps pk msg.toList sig
      check st "Lean verify accepts Lean-signed sig" leanVerify
  IO.println ""

  -- ── 11. Second key pair (different seed) ──────────
  IO.println "11. Second key pair (different seed)"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (0xFF - i).toUInt8
    let seedBA := vectorToByteArray seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
    let pkB := serializePK65 pk
    let skB := serializeSK65 sk
    check st "pk: Lean spec = mldsa-native (2nd)" (pkB == pkRef)
      s!"Lean={toHex pkB} ref={toHex pkRef}"
    check st "sk: Lean spec = mldsa-native (2nd)" (skB == skRef)
      s!"Lean={toHex skB} ref={toHex skRef}"
  IO.println ""

  -- ── 12. Corrupted signature rejection ─────────────
  IO.println "12. Corrupted signature rejection"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 3).toUInt8
    let seedBA := vectorToByteArray seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed

    let msg : ByteArray := ⟨#[0x54, 0x65, 0x73, 0x74]⟩  -- "Test"
    let rndZero : ByteArray := ⟨Array.replicate 32 0⟩

    let sigRef := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msg rndZero

    let corruptedSig := sigRef.set! 0 (sigRef[0]! ^^^ 0xFF)
    let verCorruptRef := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg corruptedSig
    check st "mldsa-native rejects corrupted sig" (verCorruptRef == 0)

    let mu' := mldsa65Primitives.hashMessage sk.tr msg.toList
    let rnd' : Bytes 32 := Vector.ofFn fun _ => 0
    let rhoDP' := mldsa65Primitives.hashPrivateSeed sk.key rnd' mu'
    let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
      sk (mldsa65Primitives.expandA pk.rho) mu' rhoDP' 256
    match sigLean with
    | none =>
      check st "Lean signing should succeed for rejection test" false
    | some sig =>
      let sigB := serializeSig65 sig
      let encM := mldsa65Encoding
      let corruptedSigB := sigB.set! 0 (sigB[0]! ^^^ 0xFF)
      match encM.sigDecode corruptedSigB with
      | none =>
        check st "Lean rejects corrupted sig (decode failure)" true
      | some (cTilde', z', h') =>
        let corruptedSigLean :
            FIPSSignature mldsa65 mldsa65Primitives :=
          ⟨cTilde', z', h'⟩
        let leanVer := fipsVerify mldsa65 mldsa65Primitives
          concreteNTTRingOps pk msg.toList corruptedSigLean
        check st "Lean rejects corrupted sig" (!leanVer)
  IO.println ""

  -- ── 13. NIST ACVP keygen vectors ──────────────────
  IO.println "13. NIST ACVP keygen vectors (ML-DSA-65)"
  do
    for vec in ACVP.keyGenVectors do
      let seedBA := parseHex vec.seed
      let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => seedBA[i]!

      let (pk, _sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
      let pkB := serializePK65 pk

      let pkExpFirst32 := parseHex vec.pkFirst32
      let pkFirst32 := pkB.extract 0 32
      check st s!"tcId={vec.tcId} pk first 32 bytes match ACVP"
        (pkFirst32 == pkExpFirst32)
        s!"got={toHex pkFirst32 32} exp={toHex pkExpFirst32 32}"
      let (pkRef, _skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
      check st s!"tcId={vec.tcId} pk: Lean = mldsa-native" (pkB == pkRef)
  IO.println ""
  -- ── 14. ML-DSA-44 and ML-DSA-87: Lean vs native ──────
  IO.println "14. ML-DSA-44 and ML-DSA-87: Lean vs native"
  do
    let seed44 : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 11 % 256).toUInt8
    let seedBA44 := vectorToByteArray seed44
    let (pk44, sk44) := keyGenFromSeed mldsa44 mldsa44Primitives concreteNTTRingOps seed44
    let (pkRef44, skRef44) := MLDSA.Concrete.FFI.mldsa44KeypairInternal seedBA44

    let enc44 := mldsa44Encoding
    let pkB44 : ByteArray := enc44.pkEncode pk44.rho pk44.t1
    let skB44 : ByteArray := enc44.skEncode sk44.rho sk44.key sk44.tr sk44.s1 sk44.s2 sk44.t0
    check st "ML-DSA-44 pk: Lean = native" (pkB44 == pkRef44)
    check st "ML-DSA-44 sk: Lean = native" (skB44 == skRef44)

    let msg44 : ByteArray := ⟨#[0x41, 0x42, 0x43]⟩
    let rndZero : ByteArray := ⟨Array.replicate 32 0⟩
    let sigRef44 := MLDSA.Concrete.FFI.mldsa44SignInternal skRef44 msg44 rndZero
    let mu44 := mldsa44Primitives.hashMessage sk44.tr msg44.toList
    let rnd44 : Bytes 32 := Vector.ofFn fun _ => (0 : UInt8)
    let rhoDP44 := mldsa44Primitives.hashPrivateSeed sk44.key rnd44 mu44
    let aHat44 := mldsa44Primitives.expandA pk44.rho
    let sigOpt44 := fipsSignLoop mldsa44 mldsa44Primitives concreteNTTRingOps
      sk44 aHat44 mu44 rhoDP44 256
    match sigOpt44 with
    | none => check st "ML-DSA-44 sign should succeed" false
    | some sig44 =>
      let sigB44 : ByteArray := enc44.sigEncode sig44.cTilde sig44.z sig44.h
      check st "ML-DSA-44 sig: Lean = native" (sigB44 == sigRef44)
      let verRef44 := MLDSA.Concrete.FFI.mldsa44VerifyInternal pkRef44 msg44 sigRef44
      check st "ML-DSA-44 native verify" (verRef44 == 1)
      let ver44 := fipsVerify mldsa44 mldsa44Primitives concreteNTTRingOps pk44 msg44.toList sig44
      check st "ML-DSA-44 Lean verify" ver44

    let seed87 : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (0xFF - (i * 9 % 256)).toUInt8
    let seedBA87 := vectorToByteArray seed87
    let (pk87, sk87) := keyGenFromSeed mldsa87 mldsa87Primitives concreteNTTRingOps seed87
    let (pkRef87, skRef87) := MLDSA.Concrete.FFI.mldsa87KeypairInternal seedBA87

    let enc87 := mldsa87Encoding
    let pkB87 : ByteArray := enc87.pkEncode pk87.rho pk87.t1
    let skB87 : ByteArray := enc87.skEncode sk87.rho sk87.key sk87.tr sk87.s1 sk87.s2 sk87.t0
    check st "ML-DSA-87 pk: Lean = native" (pkB87 == pkRef87)
    check st "ML-DSA-87 sk: Lean = native" (skB87 == skRef87)

    let msg87 : ByteArray := ⟨#[0x58, 0x59, 0x5A]⟩
    let sigRef87 := MLDSA.Concrete.FFI.mldsa87SignInternal skRef87 msg87 rndZero
    let mu87 := mldsa87Primitives.hashMessage sk87.tr msg87.toList
    let rnd87 : Bytes 32 := Vector.ofFn fun _ => (0 : UInt8)
    let rhoDP87 := mldsa87Primitives.hashPrivateSeed sk87.key rnd87 mu87
    let aHat87 := mldsa87Primitives.expandA pk87.rho
    let sigOpt87 := fipsSignLoop mldsa87 mldsa87Primitives concreteNTTRingOps
      sk87 aHat87 mu87 rhoDP87 256
    match sigOpt87 with
    | none => check st "ML-DSA-87 sign should succeed" false
    | some sig87 =>
      let sigB87 : ByteArray := enc87.sigEncode sig87.cTilde sig87.z sig87.h
      check st "ML-DSA-87 sig: Lean = native" (sigB87 == sigRef87)
      let verRef87 := MLDSA.Concrete.FFI.mldsa87VerifyInternal pkRef87 msg87 sigRef87
      check st "ML-DSA-87 native verify" (verRef87 == 1)
      let ver87 := fipsVerify mldsa87 mldsa87Primitives concreteNTTRingOps pk87 msg87.toList sig87
      check st "ML-DSA-87 Lean verify" ver87
  IO.println ""

  -- ── 15. ACVP signing vectors: Lean spec vs mldsa-native ──
  IO.println "15. ACVP signing vectors: Lean spec vs mldsa-native"
  do
    for vec in ACVP.sigGenVectors do
      let seedBA := parseHex vec.seed
      let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => seedBA[i]!
      let msgBA := parseHex vec.message

      let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
      let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed

      let rndZero : ByteArray := ⟨Array.replicate 32 0⟩
      let sigRef := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msgBA rndZero
      check st s!"sigGen tcId={vec.tcId} native sig size = 3309" (sigRef.size == 3309)

      let mu := mldsa65Primitives.hashMessage sk.tr msgBA.toList
      let rnd : Bytes 32 := Vector.ofFn fun _ => 0
      let rhoDP := mldsa65Primitives.hashPrivateSeed sk.key rnd mu
      let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
        sk (mldsa65Primitives.expandA pk.rho) mu rhoDP 256
      match sigLean with
      | none => check st s!"sigGen tcId={vec.tcId} Lean sign succeeds" false
      | some sig =>
        let sigB := serializeSig65 sig
        check st s!"sigGen tcId={vec.tcId} sig: Lean = native" (sigB == sigRef)
          s!"Lean={toHex sigB} ref={toHex sigRef}"
        let verRef := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msgBA sigRef
        check st s!"sigGen tcId={vec.tcId} native verify" (verRef == 1)
        let leanVer := fipsVerify mldsa65 mldsa65Primitives concreteNTTRingOps pk msgBA.toList sig
        check st s!"sigGen tcId={vec.tcId} Lean verify" leanVer
  IO.println ""

  -- ── 16. Cross-implementation verification ────────────
  IO.println "16. Cross-implementation verification"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 7 + 3).toUInt8
    let seedBA := vectorToByteArray seed
    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA

    let msg : ByteArray := ⟨#[0x43, 0x72, 0x6F, 0x73, 0x73]⟩
    let rndZero : ByteArray := ⟨Array.replicate 32 0⟩

    let sigNative := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msg rndZero
    let verNativeByNative := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg sigNative
    check st "native-signed, native-verified" (verNativeByNative == 1)

    let enc := mldsa65Encoding
    match enc.sigDecode sigNative with
    | none => check st "Lean decode of native sig" false
    | some (cTilde, z, h) =>
      let nativeSig : FIPSSignature mldsa65 mldsa65Primitives := ⟨cTilde, z, h⟩
      let leanVerNativeSig := fipsVerify mldsa65 mldsa65Primitives
        concreteNTTRingOps pk msg.toList nativeSig
      check st "native-signed, Lean-verified" leanVerNativeSig

    let mu := mldsa65Primitives.hashMessage sk.tr msg.toList
    let rnd : Bytes 32 := Vector.ofFn fun _ => 0
    let rhoDP := mldsa65Primitives.hashPrivateSeed sk.key rnd mu
    let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
      sk (mldsa65Primitives.expandA pk.rho) mu rhoDP 256
    match sigLean with
    | none => check st "Lean signing for cross-verify" false
    | some sig =>
      let sigB := serializeSig65 sig
      let verLeanByNative := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg sigB
      check st "Lean-signed, native-verified" (verLeanByNative == 1)
  IO.println ""

  -- ── 17. Batch FFI tests (10 seed/message pairs) ────────
  IO.println "17. Batch FFI tests (10 seed/message pairs)"
  do
    let seeds : Array (Bytes 32) := #[
      Vector.ofFn fun _ => (0 : UInt8),
      Vector.ofFn fun _ => (0xFF : UInt8),
      Vector.ofFn fun ⟨i, _⟩ => i.toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => (0xFF - i).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => (i * 7 + 13).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => ((i * 31) % 256).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => ((i * 17 + 42) % 256).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => (i * 3).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => ((i * 53 + 97) % 256).toUInt8,
      Vector.ofFn fun ⟨i, _⟩ => ((i * i) % 256).toUInt8
    ]
    let msgs : Array ByteArray := #[
      ⟨#[]⟩,
      ⟨#[0x41]⟩,
      ⟨#[0x48, 0x65, 0x6C, 0x6C, 0x6F]⟩,
      ByteArray.mk (Array.replicate 128 0xAA),
      ByteArray.mk (Array.replicate 1 0),
      ByteArray.mk (Array.replicate 256 0x55),
      ⟨#[0x00, 0xFF]⟩,
      ByteArray.mk (Array.replicate 500 0x77),
      ⟨#[0x01, 0x02, 0x03]⟩,
      ByteArray.mk (Array.replicate 1000 0xDE)
    ]
    for i in [0:seeds.size] do
      let seed := seeds[i]!
      let msg := msgs[i]!
      let seedBA := vectorToByteArray seed

      let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
      let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
      let pkB := serializePK65 pk
      let skB := serializeSK65 sk
      check st s!"batch[{i}] pk: Lean = native" (pkB == pkRef)
      check st s!"batch[{i}] sk: Lean = native" (skB == skRef)

      let rndZero : ByteArray := ⟨Array.replicate 32 0⟩
      let sigRef := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msg rndZero
      let mu := mldsa65Primitives.hashMessage sk.tr msg.toList
      let rnd : Bytes 32 := Vector.ofFn fun _ => 0
      let rhoDP := mldsa65Primitives.hashPrivateSeed sk.key rnd mu
      let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
        sk (mldsa65Primitives.expandA pk.rho) mu rhoDP 256
      match sigLean with
      | none => check st s!"batch[{i}] Lean sign" false
      | some sig =>
        let sigB := serializeSig65 sig
        check st s!"batch[{i}] sig: Lean = native" (sigB == sigRef)
        let verRef := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg sigRef
        check st s!"batch[{i}] native verify" (verRef == 1)
        let leanVer := fipsVerify mldsa65 mldsa65Primitives concreteNTTRingOps pk msg.toList sig
        check st s!"batch[{i}] Lean verify" leanVer
  IO.println ""

  -- ── 18. Edge cases and negative tests ────────────────
  IO.println "18. Edge cases and negative tests"
  do
    let seed : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 11 + 5).toUInt8
    let seedBA := vectorToByteArray seed
    let (pk, sk) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed
    let (pkRef, skRef) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA
    let rndZero : ByteArray := ⟨Array.replicate 32 0⟩

    let longMsg := ByteArray.mk (Array.replicate 10000 0xAB)
    let sigRefLong := MLDSA.Concrete.FFI.mldsa65SignInternal skRef longMsg rndZero
    let muLong := mldsa65Primitives.hashMessage sk.tr longMsg.toList
    let rnd : Bytes 32 := Vector.ofFn fun _ => 0
    let rhoDPLong := mldsa65Primitives.hashPrivateSeed sk.key rnd muLong
    let sigLeanLong := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
      sk (mldsa65Primitives.expandA pk.rho) muLong rhoDPLong 256
    match sigLeanLong with
    | none => check st "long msg (10KB): Lean sign" false
    | some sig =>
      let sigB := serializeSig65 sig
      check st "long msg (10KB): sig Lean = native" (sigB == sigRefLong)
      let verRef := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef longMsg sigRefLong
      check st "long msg (10KB): native verify" (verRef == 1)
      let leanVer := fipsVerify mldsa65 mldsa65Primitives concreteNTTRingOps pk longMsg.toList sig
      check st "long msg (10KB): Lean verify" leanVer

    let seed2 : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 19 + 7).toUInt8
    let seedBA2 := vectorToByteArray seed2
    let (pk2, _sk2) := keyGenFromSeed mldsa65 mldsa65Primitives concreteNTTRingOps seed2
    let (pkRef2, _skRef2) := MLDSA.Concrete.FFI.mldsa65KeypairInternal seedBA2

    let msg : ByteArray := ⟨#[0x57, 0x72, 0x6F, 0x6E, 0x67]⟩
    let sigRef := MLDSA.Concrete.FFI.mldsa65SignInternal skRef msg rndZero
    let verWrongKeyNative := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef2 msg sigRef
    check st "wrong key: native rejects" (verWrongKeyNative == 0)

    let enc := mldsa65Encoding
    let mu := mldsa65Primitives.hashMessage sk.tr msg.toList
    let rhoDP := mldsa65Primitives.hashPrivateSeed sk.key rnd mu
    let sigLean := fipsSignLoop mldsa65 mldsa65Primitives concreteNTTRingOps
      sk (mldsa65Primitives.expandA pk.rho) mu rhoDP 256
    match sigLean with
    | none => check st "wrong key: Lean sign" false
    | some sig =>
      let leanVerWrongKey := fipsVerify mldsa65 mldsa65Primitives
        concreteNTTRingOps pk2 msg.toList sig
      check st "wrong key: Lean rejects" (!leanVerWrongKey)

    let sigRefTrunc := sigRef.extract 0 (sigRef.size - 1)
    let verTruncNative := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef msg sigRefTrunc
    check st "truncated sig: native rejects" (verTruncNative == 0)

    match enc.sigDecode sigRefTrunc with
    | none => check st "truncated sig: Lean decode fails (expected)" true
    | some (cTilde, z, h) =>
      let truncSig : FIPSSignature mldsa65 mldsa65Primitives := ⟨cTilde, z, h⟩
      let leanVerTrunc := fipsVerify mldsa65 mldsa65Primitives
        concreteNTTRingOps pk msg.toList truncSig
      check st "truncated sig: Lean rejects" (!leanVerTrunc)

    let corruptedMsg := msg.set! 0 (msg[0]! ^^^ 0xFF)
    let verCorruptMsgNative := MLDSA.Concrete.FFI.mldsa65VerifyInternal pkRef corruptedMsg sigRef
    check st "corrupted msg: native rejects" (verCorruptMsgNative == 0)

    match enc.sigDecode sigRef with
    | none => check st "corrupted msg: Lean decode" false
    | some (cTilde, z, h) =>
      let origSig : FIPSSignature mldsa65 mldsa65Primitives := ⟨cTilde, z, h⟩
      let leanVerCorruptMsg := fipsVerify mldsa65 mldsa65Primitives
        concreteNTTRingOps pk corruptedMsg.toList origSig
      check st "corrupted msg: Lean rejects" (!leanVerCorruptMsg)
  IO.println ""

  let s ← st.get
  IO.println s!"=== {s.passed} passed, {s.failed} failed ==="
  if s.failed > 0 then
    IO.Process.exit 1

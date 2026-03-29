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
  -- ── 14. ML-DSA-44 and ML-DSA-87 internal roundtrip ─
  IO.println "14. ML-DSA-44 and ML-DSA-87 internal roundtrip"
  do
    let seed44 : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (i * 11 % 256).toUInt8
    let (pk44, sk44) := keyGenFromSeed mldsa44 mldsa44Primitives concreteNTTRingOps seed44
    let msg44 : List Byte := [0x41, 0x42, 0x43]
    let mu44 := mldsa44Primitives.hashMessage sk44.tr msg44
    let rnd44 : Bytes 32 := Vector.ofFn fun _ => (0 : UInt8)
    let rhoDP44 := mldsa44Primitives.hashPrivateSeed sk44.key rnd44 mu44
    let aHat44 := mldsa44Primitives.expandA pk44.rho
    let sigOpt44 := fipsSignLoop mldsa44 mldsa44Primitives concreteNTTRingOps
      sk44 aHat44 mu44 rhoDP44 256
    match sigOpt44 with
    | none => check st "ML-DSA-44 sign should succeed" false
    | some sig44 =>
      let ver44 := fipsVerify mldsa44 mldsa44Primitives concreteNTTRingOps pk44 msg44 sig44
      check st "ML-DSA-44 sign/verify roundtrip" ver44
    let seed87 : Bytes 32 := Vector.ofFn fun ⟨i, _⟩ => (0xFF - (i * 9 % 256)).toUInt8
    let (pk87, sk87) := keyGenFromSeed mldsa87 mldsa87Primitives concreteNTTRingOps seed87
    let msg87 : List Byte := [0x58, 0x59, 0x5A]
    let mu87 := mldsa87Primitives.hashMessage sk87.tr msg87
    let rnd87 : Bytes 32 := Vector.ofFn fun _ => (0 : UInt8)
    let rhoDP87 := mldsa87Primitives.hashPrivateSeed sk87.key rnd87 mu87
    let aHat87 := mldsa87Primitives.expandA pk87.rho
    let sigOpt87 := fipsSignLoop mldsa87 mldsa87Primitives concreteNTTRingOps
      sk87 aHat87 mu87 rhoDP87 256
    match sigOpt87 with
    | none => check st "ML-DSA-87 sign should succeed" false
    | some sig87 =>
      let ver87 := fipsVerify mldsa87 mldsa87Primitives concreteNTTRingOps pk87 msg87 sig87
      check st "ML-DSA-87 sign/verify roundtrip" ver87
  IO.println ""
  let s ← st.get
  IO.println s!"=== {s.passed} passed, {s.failed} failed ==="
  if s.failed > 0 then
    IO.Process.exit 1

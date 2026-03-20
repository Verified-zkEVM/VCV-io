/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.MLKEM.Primitives
import Examples.MLKEM.Concrete.NTT
import Examples.MLKEM.Concrete.Encoding
import Examples.MLKEM.Concrete.CBD
import Examples.MLKEM.Concrete.FFI

/-!
# Concrete ML-KEM Instance

Wires the pure-Lean NTT, encoding, and CBD implementations together with the FFI-backed
SHA-3 / SHAKE primitives to produce fully executable `NTTRingOps`, `Encoding`, and `Primitives`
instances for ML-KEM.
-/

set_option autoImplicit false

namespace MLKEM.Concrete

open MLKEM

/-! ## Conversion helpers -/

private def vectorToByteArray {n : Nat} (v : Vector UInt8 n) : ByteArray :=
  ByteArray.mk v.toArray

private def byteArrayToVector (ba : ByteArray) (offset : Nat) (n : Nat) : Vector UInt8 n :=
  Vector.ofFn fun ⟨i, _⟩ => ba.get! (offset + i)

/-! ## SampleNTT (FIPS 203 Algorithm 7) — rejection sampling from SHAKE-128 -/

/-- Rejection-sample 256 NTT-domain coefficients from a SHAKE-128 byte stream.
    Each 3-byte group yields up to two candidates `d₁, d₂ ∈ [0, 4096)`;
    a candidate is accepted iff it is `< q = 3329`. -/
private def rejectionSample (stream : ByteArray) : Array Coeff := Id.run do
  let mut acc : Array Coeff := Array.mkEmpty 256
  let numChunks := stream.size / 3
  for chunk in [0:numChunks] do
    if acc.size < 256 then
      let pos := chunk * 3
      let b0 := stream.get! pos |>.toNat
      let b1 := stream.get! (pos + 1) |>.toNat
      let b2 := stream.get! (pos + 2) |>.toNat
      let d1 := b0 + 256 * (b1 % 16)
      let d2 := b1 / 16 + 16 * b2
      if d1 < modulus && acc.size < 256 then
        acc := acc.push (d1 : Coeff)
      if d2 < modulus && acc.size < 256 then
        acc := acc.push (d2 : Coeff)
  return acc

/-- Reject silent zero-padding by requiring a full 256-coefficient output. -/
private def requireFullRejectionSample (coeffs : Array Coeff) : Array Coeff :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-KEM rejection sampler produced {coeffs.size} coefficients; expected {ringDegree}"

/-- FIPS 203 Algorithm 7: sample an NTT-domain polynomial from `SHAKE-128(ρ ‖ j ‖ i)`. -/
def concreteSampleNTT (rho : Seed32) (j i : Nat) : Tq :=
  let input := vectorToByteArray rho |>.push j.toUInt8 |>.push i.toUInt8
  -- A fixed 840-byte squeeze is enough to cover the acceptance process in practice.
  let stream := FFI.shake128 input 840
  let coeffs := requireFullRejectionSample (rejectionSample stream)
  ⟨Vector.ofFn fun ⟨idx, _⟩ => coeffs.getD idx 0⟩

/-- Exposed wrapper around `rejectionSample` for testing. -/
def rejectionSampleForTest (stream : ByteArray) : Tq :=
  let coeffs := requireFullRejectionSample (rejectionSample stream)
  ⟨Vector.ofFn fun ⟨idx, _⟩ => coeffs.getD idx 0⟩

/-! ## PRF + CBD (FIPS 203 Algorithms 6 + 8) -/

/-- `PRF_η(σ, N) = SHAKE-256(σ ‖ N, 64η)` followed by `CBD_η`. -/
private def prfCBD (eta : Nat) (sigma : Seed32) (n : Nat) : Rq :=
  let input := vectorToByteArray sigma |>.push n.toUInt8
  let prfOutput := FFI.shake256 input (64 * eta).toUSize
  samplePolyCBD eta prfOutput

/-! ## Hash wrappers -/

/-- `G(input) = SHA3-512(input)`, split into two 32-byte halves. -/
private def hashG (input : ByteArray) : Seed32 × Seed32 :=
  let hash := FFI.sha3_512 input
  (byteArrayToVector hash 0 32, byteArrayToVector hash 32 32)

/-- `H(input) = SHA3-256(input)` as a 32-byte vector. -/
private def hashH (input : ByteArray) : Vector UInt8 32 :=
  byteArrayToVector (FFI.sha3_256 input) 0 32

/-! ## Concrete `Primitives` instance -/

/-- Build the concrete `Primitives` instance for a given parameter set and encoding. -/
def concretePrimitives (params : Params) (encoding : Encoding params)
    (hEnc : encoding.EncodedTHat = ByteArray)
    (hU : encoding.EncodedU = ByteArray)
    (hV : encoding.EncodedV = ByteArray) :
    Primitives params encoding where
  gKeygen := fun d =>
    hashG (vectorToByteArray d |>.push params.k.toUInt8)
  sampleNTT := fun rho j i =>
    concreteSampleNTT rho j.val i.val
  prfEta1 := prfCBD params.eta1
  prfEta2 := prfCBD params.eta2
  gEncaps := fun m ekHash =>
    hashG (vectorToByteArray m ++ vectorToByteArray ekHash)
  hEncapsulationKey := fun tHatEncoded rho =>
    hashH (hEnc ▸ tHatEncoded ++ vectorToByteArray rho)
  jReject := fun z uEncoded vEncoded =>
    byteArrayToVector
      (FFI.shake256 (vectorToByteArray z ++ hU ▸ uEncoded ++ hV ▸ vEncoded) 32) 0 32

/-! ## Assembled ML-KEM-768 bundle -/

/-- Concrete encoding for ML-KEM-768. -/
def mlkem768Encoding : Encoding mlkem768 := concreteEncoding mlkem768

/-- Concrete encoding for ML-KEM-512. -/
def mlkem512Encoding : Encoding mlkem512 := concreteEncoding mlkem512

/-- Concrete encoding for ML-KEM-1024. -/
def mlkem1024Encoding : Encoding mlkem1024 := concreteEncoding mlkem1024

/-- Encoding roundtrip laws for ML-KEM-512. -/
def mlkem512EncodingLaws : mlkem512Encoding.Laws :=
  concreteEncodingLaws mlkem512
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Encoding roundtrip laws for ML-KEM-768. -/
def mlkem768EncodingLaws : mlkem768Encoding.Laws :=
  concreteEncodingLaws mlkem768
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Encoding roundtrip laws for ML-KEM-1024. -/
def mlkem1024EncodingLaws : mlkem1024Encoding.Laws :=
  concreteEncodingLaws mlkem1024
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Concrete primitives for ML-KEM-512. -/
def mlkem512Primitives : Primitives mlkem512 mlkem512Encoding :=
  concretePrimitives mlkem512 mlkem512Encoding rfl rfl rfl

/-- Concrete primitives for ML-KEM-768. -/
def mlkem768Primitives : Primitives mlkem768 mlkem768Encoding :=
  concretePrimitives mlkem768 mlkem768Encoding rfl rfl rfl

/-- Concrete primitives for ML-KEM-1024. -/
def mlkem1024Primitives : Primitives mlkem1024 mlkem1024Encoding :=
  concretePrimitives mlkem1024 mlkem1024Encoding rfl rfl rfl

end MLKEM.Concrete

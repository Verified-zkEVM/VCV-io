/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.Crypto.FFI
import Examples.ML_DSA.Concrete.Encoding
import Examples.ML_DSA.Concrete.NTT

/-!
# Concrete Sampling and Hash Wiring for ML-DSA

This file instantiates the SHAKE-128 / SHAKE-256 based sampling and hashing algorithms used by
FIPS 204:

- `ExpandSeed`
- `SampleInBall`
- `ExpandA`
- `ExpandS`
- `ExpandMask`
- message / commitment hash wrappers
-/

set_option autoImplicit false

namespace ML_DSA.Concrete

open ML_DSA

/-! ## SHAKE helpers -/

private def nonceLE (nonce : Nat) : ByteArray :=
  ByteArray.mk #[nonce.toUInt8, (nonce / 256).toUInt8]

private def shake256Stream (seed : ByteArray) (nonce outLen : Nat) : ByteArray :=
  Crypto.FFI.shake256 (seed ++ nonceLE nonce) outLen.toUSize

def shake256Vector (input : ByteArray) (outLen : Nat) : Vector Byte outLen :=
  byteArrayToVector (Crypto.FFI.shake256 input outLen.toUSize) 0 outLen

def hashBytes64 (input : ByteArray) : Bytes 64 :=
  shake256Vector input 64

/-! ## ExpandSeed -/

def expandSeed (seed : Bytes 32) (p : Params) : Bytes 32 × Bytes 64 × Bytes 32 :=
  let input := vectorToByteArray seed |>.push p.k.toUInt8 |>.push p.l.toUInt8
  let out := Crypto.FFI.shake256 input 128
  (byteArrayToVector out 0 32, byteArrayToVector out 32 64, byteArrayToVector out 96 32)

/-! ## Uniform rejection sampling in `Tq` -/

private def rejUniformCoeffs (stream : ByteArray) : Array Coeff := Id.run do
  let mut coeffs : Array Coeff := Array.mkEmpty ringDegree
  let mut pos := 0
  while coeffs.size < ringDegree && pos + 3 ≤ stream.size do
    let b0 := (getByteD stream pos).toNat
    let b1 := (getByteD stream (pos + 1)).toNat
    let b2 := (getByteD stream (pos + 2)).toNat
    let t := (b0 + (b1 <<< 8) + (b2 <<< 16)) &&& 0x7FFFFF
    if t < modulus then
      coeffs := coeffs.push (t : Coeff)
    pos := pos + 3
  return coeffs

private def requireFullUniformSample (coeffs : Array Coeff) : Array Coeff :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-DSA uniform sampler produced {coeffs.size} coefficients; expected {ringDegree}"

/-- FIPS 204 Algorithm 30. -/
def rejNTTPoly (input : ByteArray) : Tq :=
  let stream := Crypto.FFI.shake128 input 4096
  let coeffs := requireFullUniformSample <| rejUniformCoeffs stream
  ⟨Vector.ofFn fun i => coeffs.getD i.val 0⟩

/-- FIPS 204 Algorithm 32: `ExpandA(ρ)`.
FIPS 204 specifies the input as `ρ ∥ IntegerToBytes(s, 1) ∥ IntegerToBytes(r, 1)` where
`r` is the row and `s` is the column. Since `nonceLE` writes in little-endian, passing
`row.val * 256 + col.val` produces the bytes `[col, row]` = `[s, r]` as required. -/
def expandA (rho : Bytes 32) (p : Params) : TqMatrix p.k p.l :=
  let rhoBytes := vectorToByteArray rho
  Vector.ofFn fun row =>
    Vector.ofFn fun col =>
      rejNTTPoly (rhoBytes ++ nonceLE (row.val * 256 + col.val))

/-! ## `η`-bounded secret sampling -/

private def rejEtaCoeffs (eta : Nat) (stream : ByteArray) : Array ℤ := Id.run do
  let mut coeffs : Array ℤ := Array.mkEmpty ringDegree
  let mut pos := 0
  while coeffs.size < ringDegree && pos < stream.size do
    let byte := (getByteD stream pos).toNat
    let t0 := byte &&& 0x0F
    let t1 := byte >>> 4
    if eta = 2 then
      if t0 < 15 && coeffs.size < ringDegree then
        let u0 := t0 - ((205 * t0) >>> 10) * 5
        coeffs := coeffs.push (2 - u0)
      if t1 < 15 && coeffs.size < ringDegree then
        let u1 := t1 - ((205 * t1) >>> 10) * 5
        coeffs := coeffs.push (2 - u1)
    else if eta = 4 then
      if t0 < 9 && coeffs.size < ringDegree then
        coeffs := coeffs.push (4 - t0)
      if t1 < 9 && coeffs.size < ringDegree then
        coeffs := coeffs.push (4 - t1)
    pos := pos + 1
  return coeffs

private def requireFullEtaSample (coeffs : Array ℤ) : Array ℤ :=
  if _h : coeffs.size = ringDegree then
    coeffs
  else
    panic! s!"ML-DSA eta sampler produced {coeffs.size} coefficients; expected {ringDegree}"

private def sampleEtaPoly (eta : Nat) (seed : Bytes 64) (nonce : Nat) : Rq :=
  let stream := shake256Stream (vectorToByteArray seed) nonce 1024
  let coeffs := requireFullEtaSample <| rejEtaCoeffs eta stream
  Vector.ofFn fun i => (coeffs.getD i.val 0 : Coeff)

/-- FIPS 204 Algorithm 33. -/
def expandS (rhoPrime : Bytes 64) (p : Params) : RqVec p.l × RqVec p.k :=
  let s1 : RqVec p.l := Vector.ofFn fun i => sampleEtaPoly p.eta rhoPrime i.val
  let s2 : RqVec p.k := Vector.ofFn fun i => sampleEtaPoly p.eta rhoPrime (p.l + i.val)
  (s1, s2)

/-! ## Mask expansion via `z` unpacking -/

/-- FIPS 204 Algorithm 34. -/
def expandMask (rhoPrime : Bytes 64) (kappa : ℕ) (p : Params) : RqVec p.l :=
  let seed := vectorToByteArray rhoPrime
  Vector.ofFn fun i =>
    polyZUnpack p <| shake256Stream seed (kappa + i.val) (polyZPackedBytes p)

/-! ## Challenge sampling -/

private def shake256Prefix (input : ByteArray) (len : Nat) : ByteArray :=
  Crypto.FFI.shake256 input len.toUSize

/-- FIPS 204 Algorithm 29. -/
def sampleInBall (p : Params) (seed : CommitHashBytes p) : Rq :=
  let stream := shake256Prefix (vectorToByteArray seed) 4096
  let signs := Id.run do
    let mut acc := 0
    for i in [0:8] do
      acc := acc + (getByteD stream i).toNat * 2 ^ (8 * i)
    return acc
  let coeffs : Array Coeff := Id.run do
    let mut out : Array Coeff := Array.replicate ringDegree 0
    let mut pos := 8
    let mut signIdx := 0
    for i in [ringDegree - p.tau : ringDegree] do
      let mut chosen := 0
      let mut found := false
      while !found do
        let b := (getByteD stream pos).toNat
        pos := pos + 1
        if b ≤ i then
          chosen := b
          found := true
      out := out.set! i (out.getD chosen 0)
      let sign := if ((signs / 2 ^ signIdx) % 2) = 0 then (1 : Coeff) else (-1 : Coeff)
      out := out.set! chosen sign
      signIdx := signIdx + 1
    return out
  Vector.ofFn fun i => coeffs.getD i.val 0

/-! ## Hash wrappers -/

def hashMessage (tr : Bytes 64) (msg : List Byte) : Bytes 64 :=
  hashBytes64 (vectorToByteArray tr ++ ByteArray.mk msg.toArray)

def hashPrivateSeed (key rnd : Bytes 32) (mu : Bytes 64) : Bytes 64 :=
  hashBytes64 (vectorToByteArray key ++ vectorToByteArray rnd ++ vectorToByteArray mu)

def hashCommitmentBytes (mu : Bytes 64) (w1 : ByteArray) (p : Params) : CommitHashBytes p :=
  shake256Vector (vectorToByteArray mu ++ w1) (p.lambda / 4)

def hashPublicKeyBytes (pkBytes : ByteArray) : Bytes 64 :=
  hashBytes64 pkBytes

end ML_DSA.Concrete

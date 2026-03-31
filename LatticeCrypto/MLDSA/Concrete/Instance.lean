/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLDSA.Encoding
import LatticeCrypto.MLDSA.Concrete.Rounding
import LatticeCrypto.MLDSA.Concrete.NTT
import LatticeCrypto.MLDSA.Concrete.Sampling
import LatticeCrypto.MLDSA.Concrete.Encoding

/-!
# Concrete ML-DSA Instance

Wires the concrete rounding, NTT, sampling, hashing, and byte encoding layers into the
abstract `Primitives` and `Encoding` bundles used by the ML-DSA specification.
-/


namespace MLDSA.Concrete

open MLDSA

private def hintWeightVec {k : Nat} (h : Vector Hint k) : Nat :=
  h.toList.foldl (fun acc hi => acc + MLDSA.Concrete.hintWeight hi) 0

/-- Concrete ML-DSA primitives obtained by wiring the concrete FIPS 204 algorithms into the
abstract `Primitives` interface. -/
def concretePrimitives (p : Params) : Primitives p where
  High := High
  Power2High := Power2High
  Hint := Hint
  expandSeed := fun seed => MLDSA.Concrete.expandSeed seed p
  expandA := fun rho => MLDSA.Concrete.expandA rho p
  expandS := fun rhoPrime => MLDSA.Concrete.expandS rhoPrime p
  expandMask := fun rhoPrime kappa => MLDSA.Concrete.expandMask rhoPrime kappa p
  sampleInBall := fun cTilde => MLDSA.Concrete.sampleInBall p cTilde
  hashMessage := MLDSA.Concrete.hashMessage
  hashPrivateSeed := MLDSA.Concrete.hashPrivateSeed
  hashCommitment := fun mu w1 =>
    MLDSA.Concrete.hashCommitmentBytes mu (ByteArray.mk w1.toArray) p
  hashPublicKey := fun rho t1 =>
    MLDSA.Concrete.hashPublicKeyBytes (MLDSA.Concrete.pkEncode p rho t1)
  highBits := MLDSA.Concrete.highBits p
  highBitsShift := MLDSA.Concrete.highBitsShift p
  lowBits := MLDSA.Concrete.lowBits p
  makeHint := MLDSA.Concrete.makeHint p
  useHint := MLDSA.Concrete.useHint p
  power2Round := MLDSA.Concrete.power2Round
  power2RoundShift := MLDSA.Concrete.power2RoundShift
  w1Encode := MLDSA.Concrete.w1Encode p
  hintWeight := hintWeightVec

/-- Concrete ML-DSA byte encoding bundle for a parameter set. -/
def concreteEncoding (p : Params) : Encoding p (concretePrimitives p) where
  EncodedPK := ByteArray
  EncodedSK := ByteArray
  EncodedSig := ByteArray
  pkEncode := MLDSA.Concrete.pkEncode p
  pkDecode := MLDSA.Concrete.pkDecode p
  skEncode := MLDSA.Concrete.skEncode p
  skDecode := MLDSA.Concrete.skDecode p
  sigEncode := MLDSA.Concrete.sigEncode p
  sigDecode := MLDSA.Concrete.sigDecode p

/-- Concrete primitives specialized to ML-DSA-44. -/
def mldsa44Primitives : Primitives mldsa44 :=
  concretePrimitives mldsa44

/-- Concrete primitives specialized to ML-DSA-65. -/
def mldsa65Primitives : Primitives mldsa65 :=
  concretePrimitives mldsa65

/-- Concrete primitives specialized to ML-DSA-87. -/
def mldsa87Primitives : Primitives mldsa87 :=
  concretePrimitives mldsa87

/-- Concrete encoding bundle specialized to ML-DSA-44. -/
def mldsa44Encoding : Encoding mldsa44 mldsa44Primitives :=
  concreteEncoding mldsa44

/-- Concrete encoding bundle specialized to ML-DSA-65. -/
def mldsa65Encoding : Encoding mldsa65 mldsa65Primitives :=
  concreteEncoding mldsa65

/-- Concrete encoding bundle specialized to ML-DSA-87. -/
def mldsa87Encoding : Encoding mldsa87 mldsa87Primitives :=
  concreteEncoding mldsa87

end MLDSA.Concrete

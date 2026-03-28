/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ML_DSA.Encoding
import Examples.ML_DSA.Concrete.Rounding
import Examples.ML_DSA.Concrete.NTT
import Examples.ML_DSA.Concrete.Sampling
import Examples.ML_DSA.Concrete.Encoding

/-!
# Concrete ML-DSA Instance

Wires the concrete rounding, NTT, sampling, hashing, and byte encoding layers into the
abstract `Primitives` and `Encoding` bundles used by the ML-DSA specification.
-/

set_option autoImplicit false

namespace ML_DSA.Concrete

open ML_DSA

private def hintWeightVec {k : Nat} (h : Vector Hint k) : Nat :=
  h.toList.foldl (fun acc hi => acc + ML_DSA.Concrete.hintWeight hi) 0

def concretePrimitives (p : Params) : Primitives p where
  High := High
  Power2High := Power2High
  Hint := Hint
  expandSeed := fun seed => ML_DSA.Concrete.expandSeed seed p
  expandA := fun rho => ML_DSA.Concrete.expandA rho p
  expandS := fun rhoPrime => ML_DSA.Concrete.expandS rhoPrime p
  expandMask := fun rhoPrime kappa => ML_DSA.Concrete.expandMask rhoPrime kappa p
  sampleInBall := fun cTilde => ML_DSA.Concrete.sampleInBall p cTilde
  hashMessage := ML_DSA.Concrete.hashMessage
  hashPrivateSeed := ML_DSA.Concrete.hashPrivateSeed
  hashCommitment := fun mu w1 =>
    ML_DSA.Concrete.hashCommitmentBytes mu (ByteArray.mk w1.toArray) p
  hashPublicKey := fun rho t1 =>
    ML_DSA.Concrete.hashPublicKeyBytes (ML_DSA.Concrete.pkEncode p rho t1)
  highBits := ML_DSA.Concrete.highBits p
  lowBits := ML_DSA.Concrete.lowBits p
  makeHint := ML_DSA.Concrete.makeHint p
  useHint := ML_DSA.Concrete.useHint p
  power2Round := ML_DSA.Concrete.power2Round
  power2RoundShift := ML_DSA.Concrete.power2RoundShift
  w1Encode := ML_DSA.Concrete.w1Encode p
  hintWeight := hintWeightVec

def concreteEncoding (p : Params) : Encoding p (concretePrimitives p) where
  EncodedPK := ByteArray
  EncodedSK := ByteArray
  EncodedSig := ByteArray
  pkEncode := ML_DSA.Concrete.pkEncode p
  pkDecode := ML_DSA.Concrete.pkDecode p
  skEncode := ML_DSA.Concrete.skEncode p
  skDecode := ML_DSA.Concrete.skDecode p
  sigEncode := ML_DSA.Concrete.sigEncode p
  sigDecode := ML_DSA.Concrete.sigDecode p

def mldsa44Primitives : Primitives mldsa44 :=
  concretePrimitives mldsa44

def mldsa65Primitives : Primitives mldsa65 :=
  concretePrimitives mldsa65

def mldsa87Primitives : Primitives mldsa87 :=
  concretePrimitives mldsa87

def mldsa44Encoding : Encoding mldsa44 mldsa44Primitives :=
  concreteEncoding mldsa44

def mldsa65Encoding : Encoding mldsa65 mldsa65Primitives :=
  concreteEncoding mldsa65

def mldsa87Encoding : Encoding mldsa87 mldsa87Primitives :=
  concreteEncoding mldsa87

end ML_DSA.Concrete

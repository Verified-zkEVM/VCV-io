/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.KPKE

/-!
# ML-KEM Internal Algorithms

This file models the deterministic internal algorithms from FIPS 203 Section 6.
-/


namespace MLKEM

/-- In the internal spec, the KEM encapsulation key is just the K-PKE public key. -/
abbrev EncapsulationKey (params : Params) (encoding : Encoding params) :=
  KPKE.PublicKey params encoding

/-- In the internal spec, the KEM ciphertext is just the K-PKE ciphertext. -/
abbrev Ciphertext (params : Params) (encoding : Encoding params) :=
  KPKE.Ciphertext params encoding

/-- The ML-KEM decapsulation key packages the PKE secret key, the encapsulation key, its hash,
and the fallback seed used by implicit rejection. -/
structure DecapsulationKey (params : Params) (encoding : Encoding params) where
  dkPKE : KPKE.SecretKey params encoding
  ekPKE : EncapsulationKey params encoding
  ekHash : PublicKeyHash
  z : Seed32

variable {params : Params}

/-- Hash an encapsulation key using the abstract `H` primitive. -/
def encapsulationKeyHash (encoding : Encoding params) (prims : Primitives params encoding)
    (ek : EncapsulationKey params encoding) : PublicKeyHash :=
  prims.hEncapsulationKey ek.tHatEncoded ek.rho

/-- `ML-KEM.KeyGen_internal`. -/
def keygenInternal (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (d z : Seed32) :
    EncapsulationKey params encoding × DecapsulationKey params encoding :=
  let (ekPKE, dkPKE) := KPKE.keygenFromSeed ring encoding prims d
  let ekHash := encapsulationKeyHash encoding prims ekPKE
  let dk : DecapsulationKey params encoding := {
    dkPKE := dkPKE
    ekPKE := ekPKE
    ekHash := ekHash
    z := z
  }
  (ekPKE, dk)

/-- `ML-KEM.Encaps_internal`. -/
def encapsInternal (ring : NTTRingOps) (encoding : Encoding params)
    (prims : Primitives params encoding) (ek : EncapsulationKey params encoding)
    (m : Message) : SharedSecret × Ciphertext params encoding :=
  let ekHash := encapsulationKeyHash encoding prims ek
  let (k, r) := prims.gEncaps m ekHash
  let c := KPKE.encrypt ring encoding prims ek m r
  (k, c)

/-- `ML-KEM.Decaps_internal`. -/
def decapsInternal (ring : NTTRingOps) (encoding : Encoding params)
    [DecidableEq encoding.EncodedU] [DecidableEq encoding.EncodedV]
    (prims : Primitives params encoding)
    (dk : DecapsulationKey params encoding) (c : Ciphertext params encoding) : SharedSecret :=
  let m' := KPKE.decrypt ring encoding prims dk.dkPKE c
  let (k', r') := prims.gEncaps m' dk.ekHash
  let kBar := prims.jReject dk.z c.uEncoded c.vEncoded
  let c' := KPKE.encrypt ring encoding prims dk.ekPKE m' r'
  if c = c' then k' else kBar

end MLKEM

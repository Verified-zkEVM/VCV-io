/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.MLKEM.Ring

/-!
# ML-KEM Encoding Interfaces

This file records the compression and byte-encoding operations referenced by the FIPS 203
pseudocode. In this first phase they are kept abstract, but their types match the semantic objects
consumed by the spec-level `K-PKE` and `ML-KEM` algorithms.
-/


namespace MLKEM

/-- Encoding and compression operations used by the ML-KEM pseudocode. -/
structure Encoding (params : Params) where
  EncodedTHat : Type
  EncodedU : Type
  EncodedV : Type
  byteEncode12Vec : TqVec params.k → EncodedTHat
  byteDecode12Vec : EncodedTHat → TqVec params.k
  /-- Freshly serialized public-key vectors decode back to the original semantic value. This is
  the canonicality invariant relied on by the top-level checked ML-KEM API. -/
  byteDecode12Vec_byteEncode12Vec :
    ∀ tHat : TqVec params.k, byteDecode12Vec (byteEncode12Vec tHat) = tHat
  compressDU : RqVec params.k → RqVec params.k
  decompressDU : RqVec params.k → RqVec params.k
  byteEncodeDUVec : RqVec params.k → EncodedU
  byteDecodeDUVec : EncodedU → RqVec params.k
  compressDV : Rq → Rq
  decompressDV : Rq → Rq
  byteEncodeDV : Rq → EncodedV
  byteDecodeDV : EncodedV → Rq
  compress1 : Rq → Rq
  decompress1 : Rq → Rq
  byteEncode1 : Rq → Message
  byteDecode1 : Message → Rq

namespace Encoding

variable {params : Params} (encoding : Encoding params)

/-- Roundtrip laws needed to reason about ciphertext and message encoding at the semantic layer.
These are kept separate from the executable encoding bundle so concrete implementations can expose
their proofs incrementally without blocking computation. -/
structure Laws : Prop where
  byteDecodeDUVec_byteEncodeDUVec_compressDU :
    ∀ u : RqVec params.k,
      encoding.byteDecodeDUVec (encoding.byteEncodeDUVec (encoding.compressDU u)) =
        encoding.compressDU u
  byteDecodeDV_byteEncodeDV_compressDV :
    ∀ v : Rq,
      encoding.byteDecodeDV (encoding.byteEncodeDV (encoding.compressDV v)) =
        encoding.compressDV v
  byteEncode1_byteDecode1 :
    ∀ msg : Message, encoding.byteEncode1 (encoding.byteDecode1 msg) = msg
  byteDecode1_byteEncode1_compress1 :
    ∀ v : Rq,
      encoding.byteDecode1 (encoding.byteEncode1 (encoding.compress1 v)) =
        encoding.compress1 v

/-- Canonicality check mirroring the FIPS 203 public-key modulus check. -/
def publicKeyCanonical [DecidableEq encoding.EncodedTHat]
    (tHatEncoded : encoding.EncodedTHat) : Bool :=
  encoding.byteEncode12Vec (encoding.byteDecode12Vec tHatEncoded) == tHatEncoded

@[simp] theorem publicKeyCanonical_byteEncode12Vec_eq_true
    [DecidableEq encoding.EncodedTHat] (tHat : TqVec params.k) :
    encoding.publicKeyCanonical (encoding.byteEncode12Vec tHat) = true := by
  unfold Encoding.publicKeyCanonical
  simp [encoding.byteDecode12Vec_byteEncode12Vec tHat]

/-- Ciphertext decoding into the semantic `(u, v)` pair used by decryption. -/
def decodeCiphertext (uEncoded : encoding.EncodedU) (vEncoded : encoding.EncodedV) :
    RqVec params.k × Rq :=
  (encoding.decompressDU (encoding.byteDecodeDUVec uEncoded),
    encoding.decompressDV (encoding.byteDecodeDV vEncoded))

end Encoding

end MLKEM

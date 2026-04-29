/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import LatticeCrypto.Falcon.Primitives

/-!
# Falcon Encoding Interfaces

This file defines the byte-encoding and decoding operations for Falcon keys and signatures.
In this phase they are kept abstract, matching the semantic objects consumed by the Falcon
algorithms.

## Encoding Format

- **Public key**: 1-byte header + 14·n/8 bytes for `h` (each coefficient of `h ∈ R_q` takes
  14 bits since `q = 12289 < 2^14`).
- **Secret key**: 1-byte header + encoded `(f, g, F)` (G is recovered from the NTRU equation).
- **Signature**: 1-byte header + 40-byte salt `r` + compressed `s₂` (Algorithms 17–18).

## References

- Falcon specification v1.2, Section 3.11 (key and signature formats)
- Falcon specification v1.2, Section 3.12 (Algorithms 17–18: compress/decompress)
-/


namespace Falcon

/-- Encoding and decoding operations for Falcon keys and signatures. -/
structure Encoding (p : Params) where
  /-- Encoded public key bytes. -/
  EncodedPK : Type
  /-- Encoded secret key bytes. -/
  EncodedSK : Type
  /-- Encoded signature bytes. -/
  EncodedSig : Type
  /-- Encode a public key `h ∈ R_q` into bytes.
  Format: 1-byte header (encoding logn) + 14n/8 bytes for coefficients of `h`. -/
  pkEncode : Rq p.n → EncodedPK
  /-- Decode an encoded public key back to `h ∈ R_q`. -/
  pkDecode : EncodedPK → Option (Rq p.n)
  /-- Encode a secret key `(f, g, F)` into bytes.
  `G` is not stored; it is recovered from the NTRU equation `fG - gF = q`. -/
  skEncode : IntPoly p.n → IntPoly p.n → IntPoly p.n → EncodedSK
  /-- Decode an encoded secret key. -/
  skDecode : EncodedSK → Option (IntPoly p.n × IntPoly p.n × IntPoly p.n)
  /-- Encode a signature `(salt, s₂_compressed)` into bytes.
  Format: 1-byte header + 40-byte salt + compressed s₂ bytes. -/
  sigEncode : Bytes 40 → List Byte → EncodedSig
  /-- Decode an encoded signature back to `(salt, s₂_compressed)`. -/
  sigDecode : EncodedSig → Option (Bytes 40 × List Byte)

namespace Encoding

variable {p : Params} (enc : Encoding p)

/-- Roundtrip laws for the Falcon encoding operations. -/
structure Laws : Prop where
  /-- Public key encoding roundtrip. -/
  pkDecode_pkEncode : ∀ (h : Rq p.n), enc.pkDecode (enc.pkEncode h) = some h
  /-- Secret key encoding roundtrip. -/
  skDecode_skEncode : ∀ (f g capF : IntPoly p.n),
    enc.skDecode (enc.skEncode f g capF) = some (f, g, capF)
  /-- Signature encoding roundtrip. -/
  sigDecode_sigEncode : ∀ (salt : Bytes 40) (compSig : List Byte),
    enc.sigDecode (enc.sigEncode salt compSig) = some (salt, compSig)

end Encoding

end Falcon
